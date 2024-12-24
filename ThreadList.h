//
// Created by tibigg on 12/12/2019.
//

#ifndef THREADLIST_H
#define THREADLIST_H

#include <stdbool.h>

// For verification only
#define MAX_THREADS 3
#define pthread_join(thread, value_ptr) 0
#define pthread_tryjoin_np(thread, value_ptr) 0

// Simplified thread type for verification
typedef unsigned long pthread_t;

struct thread_node {
    pthread_t thread;
    struct thread_node *next;
    struct thread_node *prev;
};

struct thread_list {
    struct thread_node *head;
    struct thread_node *tail;
};

// Add count_threads declaration
int count_threads(struct thread_list *list);

bool init_thread_list(struct thread_list *list);
struct thread_node *create_thread_node(pthread_t thread);
bool push_thread_to_list(struct thread_list *list, pthread_t thread);
void join_and_free_finished_threads_in_list(struct thread_list *list);
void join_and_free_thread_list(struct thread_list *list);
void join_and_free_head(struct thread_list *list);

// For CBMC verification only
#define __CPROVER_has_races() 0

#endif //THREADLIST_H
