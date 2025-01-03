//
// Created by tibigg on 12/12/2019.
//

#include "ThreadList.h"
#include <stdio.h>
#include <stdlib.h>

#define __USE_GNU

bool push_thread_to_list(struct thread_list *list, pthread_t thread) {
  // Validate input
  if (list == NULL || list->head == NULL || list->tail == NULL) {
    return false;
  }
  
  struct thread_node *node = create_thread_node(thread);
  if (node == NULL) {
    return false;
  }

  // No atomic section here - caller will handle atomicity
  node->prev = list->tail->prev;
  node->next = list->tail;
  list->tail->prev->next = node;
  list->tail->prev = node;
  
  // Verify list structure
  __CPROVER_assert(node->prev->next == node, "Previous link valid");
  __CPROVER_assert(node->next->prev == node, "Next link valid");
  
  return true;
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
  return true;
}

struct thread_node *create_thread_node(pthread_t thread) {
  struct thread_node *node = malloc(sizeof(struct thread_node));
  if (node == NULL) {
    return NULL;
  }
  node->thread = thread;
  // Verify thread was stored correctly
  __CPROVER_assert(node->thread == thread, "Thread stored correctly");
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
  __CPROVER_atomic_begin();
  // Memory fence to ensure visibility
  __CPROVER_fence("WWfence", "");
  
  node->prev->next = node->next;
  node->next->prev = node->prev;
  
  __CPROVER_atomic_end();
}

void verify_thread_list() {
    struct thread_list list;
    
    // Initialize list and verify success
    bool init_success = init_thread_list(&list);
    
    // Need to add assumptions about malloc success
    __CPROVER_assume(init_success);
    __CPROVER_assume(list.head != NULL);
    __CPROVER_assume(list.tail != NULL);
    
    // Verify initial state
    __CPROVER_assert(list.head != NULL, "Initial head valid");
    __CPROVER_assert(list.tail != NULL, "Initial tail valid");
    __CPROVER_assert(list.head->next == list.tail, "Initial list empty");
    
    // Add one thread
    pthread_t t1 = 1;
    bool success = push_thread_to_list(&list, t1);
    
    // Verify pointers and structure
    __CPROVER_assert(list.head != NULL, "Head still valid");
    __CPROVER_assert(list.tail != NULL, "Tail still valid");
    __CPROVER_assert(success == true, "Push operation successful");
    
    if (success) {
        struct thread_node *node = list.head->next;
        __CPROVER_assert(node != NULL, "Node exists");
        __CPROVER_assert(node != list.tail, "Node was added");
        __CPROVER_assert(node->thread == t1, "Correct thread stored");
        __CPROVER_assert(node->prev == list.head, "Previous pointer valid");
        __CPROVER_assert(node->next == list.tail, "Next pointer valid");
    }
    
    // Cleanup
    join_and_free_thread_list(&list);
}

int count_threads(struct thread_list *list) {
    int count = 0;
    struct thread_node *cur = list->head->next;
    while (cur != list->tail) {
        count++;
        cur = cur->next;
    }
    return count;
}

void verify_main(void) {
    // Simulate command line arguments
    int argc = nondet_int();
    __CPROVER_assume(argc >= 1 && argc <= 5);  // Reasonable bounds
    
    char **argv = malloc((argc + 1) * sizeof(char*));
    __CPROVER_assume(argv != NULL);
    
    // Initialize argv array with non-deterministic strings
    for(int i = 0; i < argc; i++) {
        argv[i] = malloc(10);  // Assume max 10 chars per argument
        __CPROVER_assume(argv[i] != NULL);
        for(int j = 0; j < 9; j++) {
            argv[i][j] = nondet_char();
        }
        argv[i][9] = '\0';  // Null terminate
    }
    argv[argc] = NULL;
    
    // Call main
    int result = main(argc, argv);
    
    // Verify return value
    __CPROVER_assert(result >= 0, "Main returns valid value");
    
    // Clean up
    for(int i = 0; i < argc; i++) {
        free(argv[i]);
    }
    free(argv);
}


