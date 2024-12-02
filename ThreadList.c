//
// Created by tibigg on 12/12/2019.
//

#include "ThreadList.h"
#include <stdio.h>
#include <stdlib.h>

#define __USE_GNU

bool push_thread_to_list(struct thread_list *list, pthread_t thread) {
  struct thread_node *node = create_thread_node(thread);
  if (node == NULL) {
    printf("Not enough memory for creating a new thread. Abort...");
    return false;
  }
  node->prev = list->tail->prev;
  node->next = list->tail;

  list->tail->prev->next = node;
  list->tail->prev = node;
}

bool init_thread_list(struct thread_list *list) {
  list->head = malloc(sizeof(struct thread_node));
  list->tail = malloc(sizeof(struct thread_node));
  if (list->head == NULL || list->tail == NULL) {
    return false;
  }
  list->head->next = list->tail;
  list->tail->prev = list->head;

  list->head->prev = NULL;
  list->tail->next = NULL;
}

struct thread_node *create_thread_node(pthread_t thread) {
  struct thread_node *node = malloc(sizeof(struct thread_node));
  if (node == NULL) {
    return NULL;
  }
  node->thread = thread;
  return node;
}

void remove_elem(struct thread_node *node);
void join_and_free_thread_list(struct thread_list *list) {
  struct thread_node *prv = NULL;
  struct thread_node *cur = list->head;
  while (cur != NULL) {
    prv = cur;
    cur = cur->next;
    if (prv != list->head && prv != list->tail) {
      pthread_join(prv->thread, NULL);
    }
    free(prv);
  }
}

void join_and_free_head(struct thread_list *list) {
  struct thread_node *to_remove = list->head->next;
  if (to_remove != list->tail) {
    remove_elem(to_remove);
    pthread_join(to_remove->thread, NULL);
    free(to_remove);
  }
}

void join_and_free_finished_threads_in_list(struct thread_list *list) {
  struct thread_node *prv = NULL;
  struct thread_node *cur = list->head->next;
  while (cur != list->tail) {
    prv = cur;
    cur = cur->next;
    if (pthread_tryjoin_np (prv->thread, NULL) == 0) {
      remove_elem(prv);
      free(prv);
    }
  }
}

void remove_elem(struct thread_node *node) {
  node->prev->next = node->next;
  node->next->prev = node->prev;
}
