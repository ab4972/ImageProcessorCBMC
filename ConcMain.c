#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <assert.h>
#include "Utils.h"
#include "Picture.h"
#include "PicProcess.h"
#include "PicStore.h"

#define MAX_ARGS 3
#define CMD 0

enum Process {
  LISTSTORE,
  LOAD,
  UNLOAD,
  SAVE,
  EXIT,
  INVERT,
  GRAYSCALE,
  ROTATE,
  FLIP,
  BLUR,
  NON_EXISTENT
};

struct parsed_args {
  char *argv[MAX_ARGS + 1];
  int argc;
  enum Process cmd;
  char *source;
};

struct worker {
  pthread_t pthread;
  struct worker *prev;
  struct worker *next;
  struct pic_store *pstore;
  struct parsed_args *args;
};

struct {
  struct worker *head;
  struct worker *tail;
} worker_list;

static void liststore_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void load_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void unload_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void save_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void exit_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void invert_picture_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void grayscale_picture_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void rotate_picture_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void flip_picture_wrapper(struct pic_store *pstore, struct parsed_args *args);
static void blur_picture_wrapper(struct pic_store *pstore, struct parsed_args *args);

static void (*const cmds[])(struct pic_store *, struct parsed_args *) = {
    liststore_wrapper,
    load_wrapper,
    unload_wrapper,
    save_wrapper,
    exit_wrapper,
    invert_picture_wrapper,
    grayscale_picture_wrapper,
    rotate_picture_wrapper,
    flip_picture_wrapper,
    blur_picture_wrapper
};

// size of look-up table (for safe IO error reporting)
static int no_of_cmds = sizeof(cmds) / sizeof(cmds[0]);

static struct parsed_args *get_parsed_args(char *args_line);
static void execution_loop(struct pic_store *pstore, const char *prmt);
static bool process_args_on_pstore(struct pic_store *pstore, struct parsed_args *args);
static void load_pictures_from_args(struct pic_store *pstore, char *const *argv, int argc);
static enum Process get_process(char *process_string);
static void free_parsed_args(struct parsed_args *args);
static bool is_correct_argc(struct parsed_args *args, int correct_argc);
static char *get_name_from_file_path(char *path);
static void load_picture_from_file_path(struct pic_store *pstore, char *file_path);
static void dispatch_to_worker(struct pic_store *pstore, struct parsed_args *args);
static void init_worker(struct worker *worker, struct pic_store *pstore, struct parsed_args *args);
static void init_worker_list();
static void free_worker_list();
static void add_worker_to_back_of_list(struct worker *worker);

void dispatch_to_wrapper(struct worker *worker);
// ---------- MAIN PROGRAM ---------- \\

int main(int argc, char **argv) {

  printf("Running the Interactive C Picture Processing Library... \n");
  struct pic_store pstore;
  init_picstore(&pstore);
  init_worker_list();

  load_pictures_from_args(&pstore, argv, argc);
  execution_loop(&pstore, argv[0]);

  free_worker_list();
  pic_store_free(&pstore);
  printf("Exit successful.\n");
}

static void init_worker_list() {
  worker_list.head = malloc(sizeof(struct worker));
  worker_list.tail = malloc(sizeof(struct worker));
  if (worker_list.head == NULL || worker_list.tail == NULL) {
    printf("ERROR: There is no memory available to initialise the thread list.\n");
    exit(-1);
  }

  worker_list.head->next = worker_list.tail;
  worker_list.tail->prev = worker_list.head;

  worker_list.head->prev = NULL;
  worker_list.tail->next = NULL;
}

static void load_pictures_from_args(struct pic_store *pstore, char *const *argv, int argc) {
  printf("Loading pictures parsed as arguments... \n");
  for (int i = 1; i < argc; i++) {
    load_picture_from_file_path(pstore, argv[i]);
  }
}

static void execution_loop(struct pic_store *pstore, const char *prmt) {
  size_t line_size = 100;
  char *line = NULL;
  bool is_exit = false;

  while (!is_exit) {
    // printf("%s> ", prmt);
    size_t msg = getline(&line, &line_size, stdin);
    if (msg == -1) {
      printf("An error has occured while reading. Exitting the program...");
      break;
    }
    struct parsed_args *args = get_parsed_args(line);
    is_exit = process_args_on_pstore(pstore, args);
  }
  free(line);
}

static bool process_args_on_pstore(struct pic_store *pstore, struct parsed_args *args) {
  if (args == NULL) {
    printf("No args. Do nothing.\n");
    return false;
  } else if (args->cmd == EXIT) {
    printf("Exit has been initiated. Finishing all previous processes...\n");
    free_parsed_args(args);
    return true;
  } else if (args->cmd != NON_EXISTENT) {
    dispatch_to_worker(pstore, args);
    return false;
  } else {
    printf("Command does not exist!\n");
    free_parsed_args(args);
    return false;
  }
}

static void dispatch_to_worker(struct pic_store *pstore, struct parsed_args *args) {
  struct worker *worker = malloc(sizeof(struct worker));
  if (worker == NULL) {
    printf("Not enough memory to dispatch another worker. Abort...\n");
    return;
  }
  init_worker(worker, pstore, args);
  wait_worker_started();
}

static void init_worker(struct worker *worker, struct pic_store *pstore, struct parsed_args *args) {
  add_worker_to_back_of_list(worker);
  worker->pstore = pstore;
  worker->args = args;

  pthread_create(&worker->pthread, NULL, (void *(*)(void *)) dispatch_to_wrapper, worker);
}

static void add_worker_to_back_of_list(struct worker *worker) {
  worker->prev = worker_list.tail->prev;
  worker->next = worker_list.tail;

  worker_list.tail->prev->next = worker;
  worker_list.tail->prev = worker;
}

static struct parsed_args *get_parsed_args(char *args_line) {
  if (args_line == NULL)
    return NULL;
  struct parsed_args *args = malloc(sizeof(struct parsed_args));
  if (args == NULL)
    return NULL;
  args->source = malloc(sizeof(char) * (strlen(args_line) + 1));
  if (args->source == NULL) {
    free(args);
    return NULL;
  }
  strcpy(args->source, args_line);

  args->argc = 0;
  char *save_ptr;
  for (args->argv[args->argc] = __strtok_r(args->source, " \n", &save_ptr);
       args->argv[args->argc] != NULL && args->argc <= MAX_ARGS;
       args->argv[++(args->argc)] = __strtok_r(NULL, " \n", &save_ptr));

  if (args->argc == 0) {
    /* Line is empty. Abort...*/
    free(args->source);
    free(args);
    return NULL;
  }
  args->cmd = get_process(args->argv[CMD]);

  return args;
}

static void free_parsed_args(struct parsed_args *args) {
  if (args != NULL) {
    free(args->source);
    free(args);
  }
}

static enum Process get_process(char *process_string) {
  if (strncmp(process_string, "liststore", 9) == 0) {
    return LISTSTORE;
  } else if (strncmp(process_string, "load", 5) == 0) {
    return LOAD;
  } else if (strncmp(process_string, "unload", 7) == 0) {
    return UNLOAD;
  } else if (strncmp(process_string, "save", 5) == 0) {
    return SAVE;
  } else if (strncmp(process_string, "exit", 5) == 0) {
    return EXIT;
  } else if (strncmp(process_string, "invert", 8) == 0) {
    return INVERT;
  } else if (strncmp(process_string, "grayscale", 10) == 0) {
    return GRAYSCALE;
  } else if (strncmp(process_string, "rotate", 7) == 0) {
    return ROTATE;
  } else if (strncmp(process_string, "blur", 5) == 0) {
    return BLUR;
  } else if (strncmp(process_string, "flip", 5) == 0) {
    return FLIP;
  } else {
    printf("ERROR: this process does not exist. Abort...\n");
    return NON_EXISTENT;
  }
}

void dispatch_to_wrapper(struct worker *worker) {
  struct pic_store *pstore = worker->pstore;
  struct parsed_args *args = worker->args;
  cmds[args->cmd](pstore, args);
  free_parsed_args(args);
}

/* Function wrappers */
static void liststore_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == LISTSTORE);
  if (!is_correct_argc(args, 0)) {
    broadcast_worker_started();
    return;
  }
  print_picstore(pstore);
}

#define INPUT_PATH 1

static void load_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == LOAD);
  if (!is_correct_argc(args, 2)) {
    broadcast_worker_started();
    return;
  }
  char *file_path = args->argv[INPUT_PATH];
  char *file_name = args->argv[2];
  load_picture(pstore, file_path, file_name);
}

#define FILE_NAME 1
#define OUTPUT_PATH 2

static void unload_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == UNLOAD);
  if (!is_correct_argc(args, 1)) {
    broadcast_worker_started();
    return;
  }
  unload_picture(pstore, args->argv[FILE_NAME]);
}

static void save_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == SAVE);
  if (!is_correct_argc(args, 2)) {
    broadcast_worker_started();
    return;
  }
  save_picture(pstore, args->argv[FILE_NAME], args->argv[OUTPUT_PATH]);
}
static void exit_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == EXIT);
  printf("This will just exit, nothing to do.\n");
}
static void invert_picture_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == INVERT);
  if (!is_correct_argc(args, 1)) {
    broadcast_worker_started();
    return;
  }
  apply_transf_picstore(pstore, args->argv[FILE_NAME], (void (*)(struct picture *, void *)) invert_picture, NULL);
}
static void grayscale_picture_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == GRAYSCALE);
  if (!is_correct_argc(args, 1)) {
    broadcast_worker_started();
    return;
  }
  apply_transf_picstore(pstore, args->argv[FILE_NAME], (void (*)(struct picture *, void *)) grayscale_picture, NULL);
}
static void rotate_picture_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == ROTATE);
  if (!is_correct_argc(args, 2)) {
    broadcast_worker_started();
    return;
  }
  int rotation = strtol(args->argv[1], NULL, 10);
  apply_transf_picstore(pstore, args->argv[2], (void (*)(struct picture *, void *)) rotate_picture, (void *) rotation);
}
static void flip_picture_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == FLIP);
  if (!is_correct_argc(args, 2)) {
    broadcast_worker_started();
    return;
  }
  char flip = args->argv[1][0];
  apply_transf_picstore(pstore, args->argv[2], (void (*)(struct picture *, void *)) flip_picture, (void *) flip);
}
static void blur_picture_wrapper(struct pic_store *pstore, struct parsed_args *args) {
  assert(args->cmd == BLUR);
  if (!is_correct_argc(args, 1)) {
    broadcast_worker_started();
    return;
  }
  apply_transf_picstore(pstore, args->argv[1], (void (*)(struct picture *, void *)) blur_picture, NULL);
}

static bool is_correct_argc(struct parsed_args *args, int correct_argc) {
  if ((args->argc - 1) < correct_argc) {
    printf("Not enough arguments! Abort...\n");
    return false;
  } else if ((args->argc - 1) > correct_argc) {
    printf("Too many arguments! Abort...\n");
    return false;
  }
  return true;
}

static void load_picture_from_file_path(struct pic_store *pstore, char *file_path) {
  char *file_name = get_name_from_file_path(file_path);
  load_picture(pstore, file_path, file_name);
  free(file_name);
}

static char *get_name_from_file_path(char *path) {
  char *name = NULL;
  char buffer[100];
  strcpy(buffer, path);

  char *path_without_extension;
  char *save_word = NULL;
  char *word;
  char *save_ptr;
  for (path_without_extension = __strtok_r(buffer, ".", &save_ptr),
           word = __strtok_r(path_without_extension, "/", &save_ptr);
       path_without_extension != NULL && word != NULL;
       word = __strtok_r(NULL, "/", &save_ptr)) {
    save_word = word;
  }
  if (save_word != NULL) {
    name = malloc(sizeof(char) * 100);
    if (name != NULL) {
      strcpy(name, save_word);
    }
  }

  return name;
}

static void free_worker_list() {
  struct worker *prv = NULL;
  struct worker *cur = worker_list.head;
  while (cur != NULL) {
    prv = cur;
    cur = cur->next;
    if (prv != worker_list.head && prv != worker_list.tail) {
      pthread_join(prv->pthread, NULL);
    }
    free(prv);
  }
}

