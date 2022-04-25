#include <stdlib.h>

// --- nat

struct Natural {
  uint8_t tag;
  void *pointer;
};

struct Natural_Zero {
  uint8_t tag;
};

struct Natural_Successor {
  uint8_t tag;
  struct Natural *successor;
};

struct Natural_Zero *natural_zero() {
  struct Natural_Zero *constructor = malloc(/* ... */);
  constructor->tag = 0;
  return constructor;
}

struct Natural_Successor *natural_successor(struct Natural *natural) {
  struct Natural_Successor *constructor = malloc(/* ... */);
  constructor->tag = 1;
  constructor->successor = natural;
  return constructor;
}

// --- add

struct Function {
  void *function;
  void *captures;
};

struct Natural_Add_Captures {
  struct Natural *a;
};

struct Function *natural_add_first_argument(struct Natural *a) {
  struct Function *function = malloc(/* ... */);
  function->function = natural_add_second_argument;

  struct Natural_Add_Captures *captures = malloc(/* ... */);
  captures->a = a;

  function->captures = captures;

  return function;
}

struct Natural *natural_add_second_argument(struct Natural *b, 
                            struct Natural_Add_Captures *captures) {
  struct Natural *a = captures->a;
  struct Natural *result = NULL;
  switch (a->tag) {
  case 0:
    struct Natural_Zero *zero = (struct Natural_Zero *)a;

    result = b;
    break;
  case 1:
    struct Natural_Successor *successor = (struct Natural_Successor *)a;
    struct Natural *n = successor->successor;

    struct Function *add_function_a = natural_add_first_argument(n);
    struct Natural *add_result = add_function_a->function(b, add_function_a->captures);

    result = natural_successor(add_result);
    break;
  default:
    assert(false);
  }
  return result;
}

























// --- add: end of example.

struct Natural *natural_add_second_argument(struct Natural *b, 
                            struct Natural_Add_Captures *captures) {
  struct Natural *a = captures->a;
  struct Natural *result = NULL;
  switch (a->tag) {
  case 0: // a->tag == 0
    struct Natural_Zero *zero = 
          (struct Natural_Zero *)a;
    result = b;
    break;
  case 1: // a->tag == 1
    struct Natural_Successor *successor = 
          (struct Natural_Successor *)a;
    struct Natural *n = successor->successor;

    struct Function *add_function_a = 
        natural_add_first_argument(n);

    struct Natural *add_result = 
        add_function_a->function(
            b, 
            add_function_a->captures);

    result = natural_successor(add_result);
    break;
  default:
    assert(false);
  }
  return result;
}

struct Natural *natural_add_second_argument(
        struct Natural *b, 
        struct Natural_Add_Captures *captures) {
  struct Natural *a = captures->a;
  struct Natural *result = /* add `a` and `b`*/;
  return result;
}

int main(void) {
  struct Natural *zero_a = natural_zero();
  struct Function *function_a = natural_add_first_argument(zero_a);

  struct Natural *zero_b = natural_zero();
  struct Natural *result = function_a->function(zero_b, function_a->captures);

  // Print `result`

  return 0;
}

// --- vector

struct Vector_Nil {
  uint8_t tag;
  struct Natural_Zero *length;
};

struct Vector_Cons {
  uint8_t tag;
  void *head;
  struct Natural *length;
  struct Vector *tail;
};

struct Vector {
  uint8_t tag;
  void *pointer1;
  void *pointer2;
  void *pointer3;
};

struct Vector_Nil *vector_nil() {
  struct Vector_Nil *constructor = malloc(/* ... */);
  constructor->tag = 0;
  constructor->length = natural_zero();
  return constructor;
}

struct Vector_Cons_Captures {
  void *head;
  struct Natural *length;
};

struct Function *vector_cons_first_argument(void *head) {
  struct Vector_Cons_Captures *captures = malloc(/* ... */);
  captures->head = head;

  struct Function *function = malloc(/* ... */);
  function->function = vector_cons_second_argument;
  function->captures = captures;

  return function;
}

struct Function *vector_cons_second_argument(struct Natural *length, struct Vector_Cons_Captures *captures) {
  captures->length = length;

  struct Function *function = malloc(/* ... */);
  function->function = vector_cons_third_argument;
  function->captures = captures;

  return function;
}

struct Vector_Cons *vector_cons_third_argument(struct Vector *tail, struct Vector_Cons_Captures *captures) {
  struct Vector_Cons *constructor = malloc(/* ... */);
  constructor->tag = 1;
  constructor->head = captures->head;
  constructor->length = captures->length;
  constructor->tail = tail;
  return constructor;
}

// struct Vector_Cons *constructor = malloc(sizeof(struct Vector_Cons));
// constructor->tag = 1;
// constructor->successor = argument;
// return constructor;