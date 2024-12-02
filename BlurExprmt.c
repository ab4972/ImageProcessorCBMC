#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include <sys/time.h>
#include <getopt.h>
#include "Utils.h"
#include "Picture.h"
#include "PicProcess.h"
#include "ThreadList.h"

#define MAX_NO_BLURS 5
#define max(i, j) ((i) > (j) ? (i) : (j))

static void blur_seq_wrapper(struct picture *pic);
static void blur_by_col_wrapper(struct picture *pic);
static void blur_by_row_wrapper(struct picture *pic);
static void blur_by_pix_wrapper(struct picture *pic);
static void blur_by_sector_wrapper(struct picture *pic);

// list of blur methods
static void (*const blurs[])(struct picture *) = {
    blur_seq_wrapper,
    blur_by_col_wrapper,
    blur_by_row_wrapper,
    blur_by_sector_wrapper,
    blur_by_pix_wrapper
};

// list of blur method names
static char *blur_strings[] = {
    "in_sequence",
    "by_column",
    "by_row",
    "by_sector",
    "by_pixel"
};

static void blur_row(struct picture *pic, struct picture *tmp, int row_id);
static void blur_col(struct picture *pic, struct picture *tmp, int col_id);
static void blur_pixel(struct picture *pic, struct picture *tmp, int i, int j);
static void blur_sector(struct picture *pic,
                        struct picture *tmp,
                        int w_start,
                        int h_start,
                        int w_sector_size,
                        int h_sector_size);

// size of look-up table (for safe IO error reporting)
static int no_of_blur_algs = sizeof(blurs) / sizeof(blurs[0]);

// Default file on which the blurs are being done
static char *default_test_file_path = "test_blur_in/cthulhu_square.jpg";

// Default amount of times the pictures are blurred
static int test_iterations = 1;

// Keeps track of the time each blur algorithm ran on
static long long results[MAX_NO_BLURS];

static long long current_timestamp();
static void set_optional_new_picture_and_iterations_from_args(int argc, char *const *argv);
static bool load_pictures(struct picture **pictures, char *const *argv, int argc);
static void check_blurs_correctness(struct picture **pictures);
static struct picture *get_picture_from_file_path(char *path);
static void run_blurs(struct picture **pictures);
static void save_blurs(struct picture **pictures);
static void free_pictures(struct picture **pictures);
static void print_results();
static bool image_exists_at_file_path(char *file_path);
// ---------- MAIN PROGRAM ---------- \\

int main(int argc, char **argv) {

  printf("Support Code for Running the Blur Optimisation Experiments... \n");
  printf("==============================================================\n");
  printf("Initialising experiment...\n");
  struct picture *pictures[no_of_blur_algs];

  set_optional_new_picture_and_iterations_from_args(argc, argv);

  if (!load_pictures(pictures, argv, argc)) {
    printf("Could not load picture. Abort test...\n");
    exit(-1);
  }

  printf("Finished initialisation.\n");
  printf("==============================================================\n");
  printf("Starting experiment...\n");

  printf("This experiment will be run %d time%s, and will return the average of all the iterations.\n",
         test_iterations,
         test_iterations != 1 ? "s" : "");

  for (int i = 1; i <= test_iterations; i++) {
    printf("Running iteration %d\n", i);
    run_blurs(pictures);
  }

  printf("Saving blurred pictures in memory...\n");
  save_blurs(pictures);
  check_blurs_correctness(pictures);

  printf("Finished experiment!\n");

  printf("Here are the results for each test:\n");

  print_results();

  free_pictures(pictures);
}

static void set_optional_new_picture_and_iterations_from_args(int argc, char *const *argv) {
  printf("Loading optional arguments...\n");
  int opt;
  char *new_file_path;
  while ((opt = getopt(argc, argv, "ip")) != -1) {
    switch (opt) {
      case 'i':test_iterations = max(strtol(argv[optind], NULL, 10), 1);
        break;
      case 'p':
         new_file_path = argv[optind];
        if (image_exists_at_file_path(new_file_path)) {
          default_test_file_path = new_file_path;
          printf("File at path %s was set successfully as the test picture.\n", new_file_path);
        } else {
          printf("File at path %s does not exist. Will continue testing on the default picture.\n", new_file_path);
        }
        break;
      default:break;
    }
  }
  printf("Finished loading.\n");
}

static bool image_exists_at_file_path(char *file_path) {
  struct picture *pic;
  pic = get_picture_from_file_path(file_path);
  if (pic != NULL) {
    free_image(pic->img);
    free(pic);
    return true;
  } else {
    return false;
  }
}

/* This function assumes that the first blur that was run was the sequential one,
 * and that it blurs correctly */
static void check_blurs_correctness(struct picture **pictures) {
  printf("-----------------------------------------\n");
  printf("Making sure all pictures were blurred correctly...\n");
  bool all_correct = true;
  for (int i = 1; i < no_of_blur_algs; i++) {
    char command[500];
    sprintf(command, "./picture_compare test_blur_out/%s.jpg test_blur_out/%s.jpg", blur_strings[0], blur_strings[i]);
    if (system(command) != 0) {
      printf("WARNING: picture %s was not blurred correctly\n", blur_strings[i]);
      all_correct = false;
    }
  }
  if (all_correct) {
    printf("All pictures were blurred correctly!\n");
  } else {
    printf("Some pictures did not blurr the images correctly! Double check the algorithms\n");
  }
  printf("-----------------------------------------\n");
}

static void print_results() {
  printf("==============================================================\n");
  results[0] /= test_iterations;
  long long min = results[0];
  for (int i = 1; i < no_of_blur_algs; i++) {
    results[i] /= test_iterations;
    if (min > results[i]) {
      min = results[i];
    }
  }
  for (int i = 0; i < no_of_blur_algs; i++) {
    printf("  Blurring %11s finished in %9lld milliseconds%s\n", blur_strings[i], results[i],
           results[i] == min ? "  <- FASTEST" : "");
  }
  printf("==============================================================\n");
}

static void save_blurs(struct picture **pictures) {
  for (int i = 0; i < no_of_blur_algs; i++) {
    char path[100];
    sprintf(path, "test_blur_out/%s.jpg", blur_strings[i]);
    save_picture_to_file(pictures[i], path);
  }
}

static void run_blurs(struct picture **pictures) {
  for (int i = 0; i < no_of_blur_algs; i++) {
    printf("-----------------------------------------\n");
    long long start = current_timestamp();
    printf("Started blur %s at time = %lld milliseconds\n", blur_strings[i], start);

    blurs[i](pictures[i]);

    long long end = current_timestamp();
    printf("Ended blur %s at time = %lld milliseconds\n", blur_strings[i], end);
    printf("Execution time for blur %s = %lld milliseconds\n", blur_strings[i], end - start);
    results[i] += (end - start);
  }
  printf("-----------------------------------------\n");
}

static bool load_pictures(struct picture **pictures, char *const *argv, int argc) {
  printf("Loading picture %s %d times into memory...\n", default_test_file_path, no_of_blur_algs);
  for (int i = 0; i < no_of_blur_algs; i++) {
    pictures[i] = get_picture_from_file_path(default_test_file_path);
    if (pictures[i] == NULL) {
      printf("File at path %s does not exist! Abort...", default_test_file_path);
      return false;
    }
  }
  printf("Finished loading %d pictures with width %d and height %d into memory.\n",
         no_of_blur_algs,
         pictures[0]->width,
         pictures[0]->height);
  return true;
}

static struct picture *get_picture_from_file_path(char *path) {
  struct picture *pic = malloc(sizeof(struct picture));
  if (init_picture_from_file(pic, path)) {
    return pic;
  } else {
    free(pic);
    return NULL;
  }
}

static void free_pictures(struct picture **pictures) {
  for (int i = 0; i < no_of_blur_algs; i++) {
    free_image(pictures[i]->img);
    free(pictures[i]);
  }
}

static long long current_timestamp() {
  struct timeval te;
  gettimeofday(&te, NULL);
  long long milliseconds = te.tv_sec * 1000LL + te.tv_usec / 1000;
  return milliseconds;
}

static void blur_seq_wrapper(struct picture *pic) {
  blur_picture(pic);
}

/*======================BLUR BY ROW=======================*/

static bool try_dispatch_row_blurrer(pthread_t *thread, struct picture *pic, struct picture *tmp, int row_id);
static void blur_by_row_wrapper(struct picture *pic) {
  struct picture tmp;
  tmp.img = copy_image(pic->img);
  tmp.width = pic->width;
  tmp.height = pic->height;
  struct thread_list list;
  init_thread_list(&list);
  for (int j = 1; j < tmp.height - 1; j++) {
    pthread_t blurrer;
    while (try_dispatch_row_blurrer(&blurrer, pic, &tmp, j) == false) {
      join_and_free_finished_threads_in_list(&list);
    }
    push_thread_to_list(&list, blurrer);
  }

  join_and_free_thread_list(&list);
  clear_picture(&tmp);
}

struct row_info {
  struct picture *pic;
  struct picture *tmp;
  int id;
};

static void blur_row_parallel(struct row_info *row_info);

static bool try_dispatch_row_blurrer(pthread_t *thread, struct picture *pic, struct picture *tmp, int row_id) {
  struct row_info *row_info = malloc(sizeof(struct row_info));
  if (row_info == NULL) {
    return false;
  }
  row_info->pic = pic;
  row_info->tmp = tmp;
  row_info->id = row_id;

  if (pthread_create(thread, NULL, (void *(*)(void *)) blur_row_parallel, row_info) == 0) {
    return true;
  } else {
    free(row_info);
    return false;
  }
}

static void blur_row_parallel(struct row_info *row_info) {
  blur_row(row_info->pic, row_info->tmp, row_info->id);
  free(row_info);
}

/*======================BLUR BY COLLUMN=======================*/

static bool try_dispatch_col_blurrer(pthread_t *thread, struct picture *pic, struct picture *tmp, int col_id);
static void blur_by_col_wrapper(struct picture *pic) {
  struct picture tmp;
  tmp.img = copy_image(pic->img);
  tmp.width = pic->width;
  tmp.height = pic->height;
  struct thread_list list;
  init_thread_list(&list);
  for (int i = 1; i < tmp.width - 1; i++) {
    pthread_t blurrer;
    while (try_dispatch_col_blurrer(&blurrer, pic, &tmp, i) == false) {
      join_and_free_finished_threads_in_list(&list);
    }
    push_thread_to_list(&list, blurrer);
  }

  join_and_free_thread_list(&list);
  clear_picture(&tmp);
}

struct col_info {
  struct picture *pic;
  struct picture *tmp;
  int id;
};

static void blur_col_parallel(struct col_info *col_info);

static bool try_dispatch_col_blurrer(pthread_t *thread, struct picture *pic, struct picture *tmp, int col_id) {
  struct col_info *col_info = malloc(sizeof(struct col_info));
  if (col_info == NULL) {
    return false;
  }
  col_info->pic = pic;
  col_info->tmp = tmp;
  col_info->id = col_id;

  if (pthread_create(thread, NULL, (void *(*)(void *)) blur_col_parallel, col_info) == 0) {
    return true;
  } else {
    free(col_info);
    return false;
  }
}

static void blur_col_parallel(struct col_info *col_info) {
  blur_col(col_info->pic, col_info->tmp, col_info->id);
  free(col_info);
}

/*======================BLUR BY SECTOR=======================*/

static bool try_dispatch_sector_blurrer(pthread_t *thread,
                                        struct picture *pic,
                                        struct picture *tmp,
                                        int w_start,
                                        int h_start,
                                        int w_sector_size,
                                        int h_sector_size);

static void blur_by_sector_wrapper(struct picture *pic) {
  struct picture tmp;
  tmp.img = copy_image(pic->img);
  tmp.width = pic->width;
  tmp.height = pic->height;

  // Calculate sector sizes
  int w_sector_size;
  int h_sector_size;
  if (tmp.width >= tmp.height) {
    w_sector_size = max(tmp.width / 4, 1);
    h_sector_size = max(tmp.height / 2, 1);
  } else {
    w_sector_size = max(tmp.width / 2, 1);
    h_sector_size = max(tmp.height / 4, 1);
  }

  struct thread_list list;
  init_thread_list(&list);
  for (int i = 1; i < tmp.width - 1; i += w_sector_size) {
    for (int j = 1; j < tmp.height - 1; j += h_sector_size) {
      pthread_t blurrer;
      while (try_dispatch_sector_blurrer(&blurrer, pic, &tmp, i, j, w_sector_size, h_sector_size) == false) {
        join_and_free_finished_threads_in_list(&list);
      }
      push_thread_to_list(&list, blurrer);
    }
  }

  join_and_free_thread_list(&list);
  clear_picture(&tmp);
}

struct sector_info {
  struct picture *pic;
  struct picture *tmp;
  int w_start;
  int h_start;
  int w_sector_size;
  int h_sector_size;
};

static void blur_sector_parallel(struct sector_info *sector_info);

static bool try_dispatch_sector_blurrer(pthread_t *thread,
                                        struct picture *pic,
                                        struct picture *tmp,
                                        int w_start,
                                        int h_start,
                                        int w_sector_size,
                                        int h_sector_size) {
  struct sector_info *sector_info = malloc(sizeof(struct sector_info));
  if (sector_info == NULL) {
    return false;
  }
  sector_info->pic = pic;
  sector_info->tmp = tmp;
  sector_info->w_start = w_start;
  sector_info->h_start = h_start;
  sector_info->w_sector_size = w_sector_size;
  sector_info->h_sector_size = h_sector_size;

  if (pthread_create(thread, NULL, (void *(*)(void *)) blur_sector_parallel, sector_info) == 0) {
    return true;
  } else {
    free(sector_info);
    return false;
  }
}

static void blur_sector_parallel(struct sector_info *sector_info) {
  blur_sector(sector_info->pic,
              sector_info->tmp,
              sector_info->w_start,
              sector_info->h_start,
              sector_info->w_sector_size,
              sector_info->h_sector_size);
  free(sector_info);
}

/*======================BLUR BY PIXEL=======================*/

static bool try_dispatch_pixel_blurrer(pthread_t *thread, struct picture *pic, struct picture *tmp, int i, int j);
static void blur_by_pix_wrapper(struct picture *pic) {
  struct picture tmp;
  tmp.img = copy_image(pic->img);
  tmp.width = pic->width;
  tmp.height = pic->height;
  struct thread_list list;
  init_thread_list(&list);

  for (int i = 1; i < tmp.width - 1; i++) {
    for (int j = 1; j < tmp.height - 1; j++) {
      pthread_t blurrer;
      while (try_dispatch_pixel_blurrer(&blurrer, pic, &tmp, i, j) == false) {
        join_and_free_finished_threads_in_list(&list);
      }
      push_thread_to_list(&list, blurrer);
    }
  }

  join_and_free_thread_list(&list);
  clear_picture(&tmp);
}

struct pix_info {
  struct picture *pic;
  struct picture *tmp;
  int i;
  int j;
};

static void blur_pixel_parallel(struct pix_info *pix_info);

static bool try_dispatch_pixel_blurrer(pthread_t *thread, struct picture *pic, struct picture *tmp, int i, int j) {
  struct pix_info *pix_info = malloc(sizeof(struct pix_info));
  if (pix_info == NULL) {
    return false;
  }
  pix_info->pic = pic;
  pix_info->tmp = tmp;
  pix_info->i = i;
  pix_info->j = j;

  if (pthread_create(thread, NULL, (void *(*)(void *)) blur_pixel_parallel, pix_info) == 0) {
    return true;
  } else {
    free(pix_info);
    return false;
  }
}

static void blur_pixel_parallel(struct pix_info *pix_info) {
  blur_pixel(pix_info->pic, pix_info->tmp, pix_info->i, pix_info->j);
  free(pix_info);
}

/*======================HELPER FUNCTIONS=====================*/

#define BLUR_REGION_SIZE 9

static void blur_sector(struct picture *pic,
                        struct picture *tmp,
                        int w_start,
                        int h_start,
                        int w_sector_size,
                        int h_sector_size) {
  int w_end = w_start + w_sector_size;
  int h_end = h_start + h_sector_size;
  for (int i = w_start; i < w_end && i < tmp->width - 1; i++) {
    for (int j = h_start; j < h_end && j < tmp->height - 1; j++) {
      blur_pixel(pic, tmp, i, j);
    }
  }
}

static void blur_row(struct picture *pic, struct picture *tmp, int row_id) {
  for (int i = 1; i < tmp->width - 1; i++) {
    blur_pixel(pic, tmp, i, row_id);
  }
}

static void blur_col(struct picture *pic, struct picture *tmp, int col_id) {
  for (int j = 1; j < tmp->height - 1; j++) {
    blur_pixel(pic, tmp, col_id, j);
  }
}

static void blur_pixel(struct picture *pic, struct picture *tmp, int i, int j) {
  struct pixel rgb;
  int sum_red = 0;
  int sum_green = 0;
  int sum_blue = 0;

  for (int n = -1; n <= 1; n++) {
    for (int m = -1; m <= 1; m++) {
      rgb = get_pixel(tmp, i + n, j + m);
      sum_red += rgb.red;
      sum_green += rgb.green;
      sum_blue += rgb.blue;
    }
  }

  rgb.red = sum_red / BLUR_REGION_SIZE;
  rgb.green = sum_green / BLUR_REGION_SIZE;
  rgb.blue = sum_blue / BLUR_REGION_SIZE;

  set_pixel(pic, i, j, &rgb);
}
