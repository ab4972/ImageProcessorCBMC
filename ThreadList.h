//
// Created by tibigg on 12/12/2019.
//

#ifndef TRUE_CONCURRENCY_TG4018__THREADLIST_H_
#define TRUE_CONCURRENCY_TG4018__THREADLIST_H_

#include <pthread.h>
#include <stdbool.h>

struct thread_list {
  struct thread_node *head;
  struct thread_node *tail;
};

struct thread_node {
  pthread_t thread;
  struct thread_node *prev;
  struct thread_node *next;
};


bool init_thread_list(struct thread_list *list);
struct thread_node *create_thread_node(pthread_t thread);
bool push_thread_to_list(struct thread_list *list, pthread_t thread);
void join_and_free_finished_threads_in_list(struct thread_list *list);
void join_and_free_thread_list(struct thread_list *list);
void join_and_free_head(struct thread_list *list);

#endif //TRUE_CONCURRENCY_TG4018__THREADLIST_H_
