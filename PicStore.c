#include "PicStore.h"
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include "PicProcess.h"

static void node_lock(struct pic_node *pic_node);
static void node_unlock(struct pic_node *pic_node);
static struct pic_node *pic_node_create(const char *filename, const char *path);
static void pic_node_free(struct pic_node *cur);
static void print_transform_message(const char *filename, void (*transf)(struct picture *, void *));
static void init_picstore_list(struct pic_store_list *pslist);
static void pic_store_list_free(struct pic_store_list *pslist);

static void print_picstore_list(struct pic_store_list *pslist);
static void load_picture_in_pic_list(struct pic_store_list *pslist, const char *path, const char *filename);
static void unload_picture_from_pic_list(struct pic_store_list *pslist, const char *filename);
static void save_picture_from_list(struct pic_store_list *pstore, const char *filename, const char *path);
static void apply_transf_picstore_list(struct pic_store_list *pslist,
                                       const char *filename,
                                       void (transf)(struct picture *, void *),
                                       void *aux);
static void preblock_pic_list(struct pic_store_list *pslist);

static unsigned long hash(const char *str);

void preblock_pic_store(struct pic_store *pstore);

static pthread_mutex_t worker_lock;
static pthread_cond_t worker_started;

void init_picstore(struct pic_store *pstore) {
  for (int i = 0; i < NUM_PIC_STORE_LISTS; i++) {
    pstore->table[i] = malloc(sizeof(struct pic_store_list));
    if (pstore->table[i] == NULL) {
      printf("Not enough memory for list %d. Abort!\n", i);
      pic_store_free(pstore);
      exit(0);
    } else {
      init_picstore_list(pstore->table[i]);
    }
  }

  pthread_mutex_init(&worker_lock, NULL);
  pthread_cond_init(&worker_started, NULL);
}

static void init_picstore_list(struct pic_store_list *pslist) {

  pslist->head = pic_node_create(NULL, NULL);
  pslist->tail = pic_node_create(NULL, NULL);

  // Make sure head and tail elements exist
  assert(pslist->head);
  assert(pslist->tail);
  pslist->head->next = pslist->tail;
  pslist->tail->prev = pslist->head;
}

void print_picstore(struct pic_store *pstore) {
  preblock_pic_store(pstore);
  broadcast_worker_started();
  for (int i = 0; i < NUM_PIC_STORE_LISTS; i++) {
    print_picstore_list(pstore->table[i]);
  }
}

void preblock_pic_store(struct pic_store *pstore) {
  for (int i = 0; i < NUM_PIC_STORE_LISTS; i++) {
    preblock_pic_list(pstore->table[i]);
  }
}

static void preblock_pic_list(struct pic_store_list *pslist) {
  node_lock(pslist->head);
}

// WARNING: assumes it already has blocked this list
static void print_picstore_list(struct pic_store_list *pslist) {

  // set-up for index traversal
  struct pic_node *cur = pslist->head;
  struct pic_node *nxt = cur->next;
  node_lock(nxt);
  node_unlock(cur);

  // traverse the index elements
  while (nxt != pslist->tail) {
    cur = nxt;
    nxt = cur->next;

    node_lock(nxt);
    printf("%s\n", cur->filename);
    node_unlock(cur);
  }
  node_unlock(nxt);
}

void load_picture(struct pic_store *pstore, const char *path, const char *filename) {
  // Find to which index in the table should it be loaded
  uint32_t index = (uint32_t) hash(filename) % NUM_PIC_STORE_LISTS;
  load_picture_in_pic_list(pstore->table[index], path, filename);
}

static void load_picture_in_pic_list(struct pic_store_list *pslist, const char *path, const char *filename) {
  struct pic_node *new_node = pic_node_create(filename, path);
  if (new_node == NULL) {
    printf("ERROR: file doesn't exist or system is out of memory!\n");
    broadcast_worker_started();
    return;
  }

  // set-up for index traversal
  struct pic_node *prv = NULL;
  node_lock(pslist->head);
  broadcast_worker_started();
  struct pic_node *cur = pslist->head;

  // traverse the index elements
  while (cur->next != pslist->tail) {
    node_unlock(prv);
    prv = cur;
    cur = cur->next;
    node_lock(cur);

    int cmp = strcmp(cur->filename, filename);

    if (cmp == 0) {
      printf("WARNING: file with name %s already exists, so it cannot be added again. Aborting...\n", filename);
      // we do not duplicate items in the index
      pic_node_free(new_node);
      node_unlock(cur);
      node_unlock(prv);
      return;
    }

    if (cmp > 0) {
      // found where the new item should go

      // update new Node pointers (dangles off of list for now)
      new_node->prev = prv;
      new_node->next = cur;

      // update back pointer of current element
      cur->prev = new_node;

      // update forward pointer of prev element (or list head)
      prv->next = new_node;
      node_unlock(prv);
      node_unlock(cur);
      printf("File from path %s has been added, with name %s.\n", path, filename);
      return;
    }
    // goto next element
    node_unlock(prv);
  }

  // if not inserted in loop then item belongs on the end of the list (before tail)
  pslist->tail->prev = new_node;
  new_node->next = pslist->tail;
  new_node->prev = cur;
  cur->next = new_node;

  node_unlock(cur);
  printf("File from path %s has been added, with name %s.\n", path, filename);
}

void unload_picture(struct pic_store *pstore, const char *filename) {
  // Find to which index in the table should it be loaded
  uint32_t index = (uint32_t) hash(filename) % NUM_PIC_STORE_LISTS;
  unload_picture_from_pic_list(pstore->table[index], filename);
}

static void unload_picture_from_pic_list(struct pic_store_list *pslist, const char *filename) {
  // set-up for index traversal
  struct pic_node *prv = NULL;
  struct pic_node *cur = pslist->head;
  node_lock(cur);
  broadcast_worker_started();

  struct pic_node *nxt = NULL;

  bool removed = false;
  int cmp = -1;

  // traverse the index elements
  while (!removed && cmp < 0 && cur->next != pslist->tail) {
    prv = cur;
    cur = cur->next;
    node_lock(cur);
    nxt = cur->next;

    // check each item
    if ((cmp = strcmp(cur->filename, filename)) == 0) {
      node_lock(nxt);
      // found the item to be removed
      nxt->prev = prv;

      // update forward pointer of prev element (or list head)
      prv->next = nxt;

      node_unlock(nxt);
      // free up memory for Node object
      node_unlock(cur);
      pic_node_free(cur);
      removed = true;
    }
    node_unlock(prv);
  }
  node_unlock(cur);

  if (removed) {
    printf("File with name %s removed from the store.\n", filename);
  } else {
    printf("WARNING: file with name %s does not exists in the store, so it cannot be unloaded. Aborting...\n",
           filename);
  }
}

void save_picture(struct pic_store *pstore, const char *filename, const char *path) {
  // Find to which index in the table should it be loaded
  uint32_t index = (uint32_t) hash(filename) % NUM_PIC_STORE_LISTS;
  save_picture_from_list(pstore->table[index], filename, path);
}

static void save_picture_from_list(struct pic_store_list *pstore, const char *filename, const char *path) {
  // set-up for index traversal
  struct pic_node *cur = pstore->head;
  node_lock(cur);
  broadcast_worker_started();
  struct pic_node *nxt = cur->next;
  node_lock(nxt);
  node_unlock(cur);

  bool found = false;
  int cmp;

  // traverse the index elements
  while (!found && nxt != pstore->tail && (cmp = strcmp(nxt->filename, filename)) <= 0) {
    cur = nxt;
    nxt = cur->next;

    node_lock(nxt);
    if (cmp == 0) {
      // found it!
      save_picture_to_file(&cur->pic, path);
      printf("File %s has been saved successfully to %s.\n", filename, path);
      found = true;
    }
    node_unlock(cur);
  }
  node_unlock(nxt);

  if (!found) {
    printf("WARNING: file with name %s does not exists in the store, so it cannot be saved. Aborting...\n", filename);
  }
}

void apply_transf_picstore(struct pic_store *pstore,
                           const char *filename,
                           void (transf)(struct picture *, void *),
                           void *aux) {
  // Find to which index in the table should it be loaded
  uint32_t index = (uint32_t) hash(filename) % NUM_PIC_STORE_LISTS;
  apply_transf_picstore_list(pstore->table[index], filename, transf, aux);
}

static void apply_transf_picstore_list(struct pic_store_list *pslist,
                                       const char *filename,
                                       void (transf)(struct picture *, void *),
                                       void *aux) {
  // set-up for index traversal
  node_lock(pslist->head);
  broadcast_worker_started();
  struct pic_node *cur = pslist->head;
  struct pic_node *nxt = cur->next;
  node_lock(nxt);
  node_unlock(cur);

  bool found = false;
  int cmp;

  // traverse the index elements
  while (!found && nxt != pslist->tail && (cmp = strcmp(nxt->filename, filename)) <= 0) {
    cur = nxt;
    nxt = cur->next;

    node_lock(nxt);
    if (cmp == 0) {
      // found it!

      transf(&cur->pic, aux);
      print_transform_message(filename, transf);
      found = true;
    }
    node_unlock(cur);
  }
  node_unlock(nxt);

  if (!found) {
    printf("WARNING: file with name %s does not exists in the store, so it cannot be transformed. Aborting...\n",
           filename);
  }
}

static void print_transform_message(const char *filename, void (*transf)(struct picture *, void *)) {
  char type[15];
  if (transf == (void (*)(struct picture *, void *)) invert_picture) {
    strcpy(type, "inverted");
  } else if (transf == (void (*)(struct picture *, void *)) grayscale_picture) {
    strcpy(type, "grayscaled");
  } else if (transf == (void (*)(struct picture *, void *)) rotate_picture) {
    strcpy(type, "rotated");
  } else if (transf == (void (*)(struct picture *, void *)) flip_picture) {
    strcpy(type, "flipped");
  } else if (transf == (void (*)(struct picture *, void *)) blur_picture) {
    strcpy(type, "blurred");
  } else {
    strcpy(type, "transformed");
  }
  printf("File %s has been %s successfully.\n", filename, type);
}

// Not thread safe
void pic_store_free(struct pic_store *pstore) {
  for (int i = 0; i < NUM_PIC_STORE_LISTS; i++) {
    if (pstore->table[i] != NULL) {
      pic_store_list_free(pstore->table[i]);
    }
  }
}

// Not thread safe
static void pic_store_list_free(struct pic_store_list *pslist) {
  struct pic_node *cur = pslist->head;
  struct pic_node *nxt = NULL;
  while (cur != NULL) {
    nxt = cur->next;
    pic_node_free(cur);
    cur = nxt;
  }
  free(pslist);
}

// Create basic PicNode
static struct pic_node *pic_node_create(const char *filename, const char *path) {
  struct pic_node *new_pic_node = malloc(sizeof(struct pic_node));
  if (new_pic_node == NULL) {
    return NULL;
  }
  pthread_mutex_init(&new_pic_node->lock, NULL);
  new_pic_node->prev = NULL;
  new_pic_node->next = NULL;

  if (path != NULL) {
    bool init_success = init_picture_from_file(&new_pic_node->pic, path);
    if (!init_success) {
      free(new_pic_node);
      return NULL;
    }
  } else {
    new_pic_node->pic.img.data = NULL;
  }

  if (filename != NULL) {
    new_pic_node->filename = malloc(sizeof(char) * strlen(filename));
    strcpy(new_pic_node->filename, filename);
  }

  return new_pic_node;
}

static void pic_node_free(struct pic_node *cur) {
  if (cur->pic.img.data != NULL) {
    free_image(cur->pic.img);
  }
  free(cur->filename);
  free(cur);
}

// Synchronisation primitives
static void node_lock(struct pic_node *pic_node) {
  if (pic_node) {
    pthread_mutex_lock(&pic_node->lock);
  }
}

static void node_unlock(struct pic_node *pic_node) {
  if (pic_node) {
    pthread_mutex_unlock(&pic_node->lock);
  }
}

void wait_worker_started() {
  pthread_cond_wait(&worker_started, &worker_lock);
}

void broadcast_worker_started() {
  pthread_cond_signal(&worker_started);
}

static unsigned long hash(const char *str) {
  unsigned long hash = 5381;
  int c;

  while ((c = *str++))
    hash = ((hash << 5) + hash) + c; /* hash * 33 + c */

  return hash;
}
