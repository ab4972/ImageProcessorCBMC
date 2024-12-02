#ifndef PICSTORE_H
#define PICSTORE_H

#define NUM_PIC_STORE_LISTS 17
#include "Picture.h"
#include "Utils.h"
#include <pthread.h>

// The picture node struct implements a Doubly-Linked-List element
struct pic_node {

  // lock
  pthread_mutex_t lock;
  // index value of the node
  struct picture pic;

  // picture identifier
  char *filename;

  // pointers to previous/next nodes in the list
  struct pic_node *prev;
  struct pic_node *next;

};

struct pic_store_list {
  struct pic_node *head;
  struct pic_node *tail;
};

struct pic_store {
  struct pic_store_list *table[NUM_PIC_STORE_LISTS];
};

// picture library initialisation
void init_picstore(struct pic_store *pstore);

// command-line interpreter routines
void print_picstore(struct pic_store *pstore);
void load_picture(struct pic_store *pstore, const char *path, const char *filename);
void unload_picture(struct pic_store *pstore, const char *filename);
void save_picture(struct pic_store *pstore, const char *filename, const char *path);

void apply_transf_picstore(struct pic_store *pstore,
                           const char *filename,
                           void (transf)(struct picture *, void *),
                           void *aux);

// NON THREAD SAFE freeing function
void pic_store_free(struct pic_store *pstore);

// Main thread synchronisation
void wait_worker_started();
void broadcast_worker_started();

#endif

