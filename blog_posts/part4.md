# Understanding Coq - Part 4 - Compilation

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 5 - Reflections](https://gist.github.com/justinfargnoli/b8837284d9ef53f578405976260b9330) ------- Previous post: [Part 3 - Type Checking](https://gist.github.com/justinfargnoli/8ded6d3c94bcfa82503ffd329460fd75)

##

In this blog post I'll walk through the approach I took to compile the Calculus of Inductive Constructions (CoIC).

## Table of Contents

- [Understanding Coq - Part 4 - Compilation](#understanding-coq---part-4---compilation)
  - [Table of Contents](#table-of-contents)
  - [My Implementation](#my-implementation)
  - [Running Example](#running-example)
  - [Inductives](#inductives)
  - [The Calculus of Constructions](#the-calculus-of-constructions)
    - [Function Definitions](#function-definitions)
    - [`match`](#match)
    - [DeBruijn Indexes](#debruijn-indexes)
    - [Function Call](#function-call)
    - [`add`ition](#addition)
  - [What about types?](#what-about-types)
  - [Conclusion](#conclusion)

## My Implementation

My compiler for the CoIC is on my GitHub in the [Koi](https://github.com/justinfargnoli/koi) repository in the `compiler/src/codegen` directory.

I chose to compile from the CoIC to LLVM IR. [LLVM](https://en.wikipedia.org/wiki/LLVM) is a piece of compiler infrastructure that does language-independent optimization, target code generation, and target-dependent optimization. The Clang C++ compiler, Rust, Swift, Julia, and many other programming languages use LLVM. LLVM defines an intermediate representation (IR) that compiler front ends can emit to give their code to LLVM. The `codegen` module in my implementation does just that. It generates LLVM IR, writes it to a file, and then uses `clang` to give the LLVM IR file to LLVM. 

However, in this blog post, I won't be going into detail on how I compiled the CoIC to LLVM IR. Instead, I will talk about compiling the CoIC to C. That way we can ignore some of the complexity that comes with working with LLVM. 

## Running Example

This post will use the `Natural` number type and the `add`ition function for natural numbers to illustrate the compilation process. 

```Coq
1  Inductive Natural : Set :=
2  | Zero : Natural
3  | Successor (n : Natural) : Natural. 
4
5  Fixpoint add (a : Natural) : Natural -> Natural :=
6      fun (b : Natural) =>
7         match a with
8         | Zero => b
9         | Successor (n : Natural) => Successor (add n b).
```

## Inductives

Let's look at how to compile the definition of the `Natural` number inductive type.

```Coq
1  Inductive Natural : Set :=
2  | Zero : Natural
3  | Successor (n : Natural) : Natural. 
```

From a compilation perspective, an inductive type needs structs to hold the data that's passed as arguments its constructors and functions to construct these structs. Additionally, if we think ahead to the compilation of `match` statements, we will need a mechanism to determine which variant of the inductive type we have. To resolve this we first, add a `tag` field to each constructor's corresponding struct that will store a unique integer. This integer represents which variant of the inductive type this value was constructed with. Then, we generate a generic struct `struct Inductive { ... }` that we can cast the scrutinee of our match statement to read the tag field of the struct. 

So, for the `Natural` number type we will generate:

```C
struct Inductive {
  uint8_t tag;
};

struct Natural_Zero {
  uint8_t tag;
};

struct Natural_Successor {
  uint8_t tag;
  void *successor;
};

struct Natural_Zero *natural_zero() {
  struct Natural_Zero *constructor = malloc(sizeof(struct Natural_Zero));
  constructor->tag = 0;
  return constructor;
}

struct Natural_Successor *natural_successor(struct Natural *natural) {
  struct Natural_Successor *constructor = malloc(sizeof(struct Natural_Successor));
  constructor->tag = 1;
  constructor->successor = natural;
  return constructor;
}
```

Notice that the `successor` field of `Natural_Successor` is a `void *`. This is because we don't know what type the `successor` will be. It could either be `struct Natural_Zero` or `struct Natural_Successor`. We won't know until we cast `successor` to a `struct Inductive` and look at its `tag`.

## The Calculus of Constructions

Let's look at how to compile the definition of the `add` function.

```Coq
5  Fixpoint add (a : Natural) : Natural -> Natural :=
6      fun (b : Natural) =>
7         match a with
8         | Zero => b
9         | Successor (n : Natural) => Successor (add n b).
```

### Function Definitions

In this sub-section we'll examine how to compile the following code:

```Coq
5  Fixpoint add (a : Natural) : Natural -> Natural :=
6      fun (b : Natural) := (* ignored *).
```

To compile the `add` function we need to compile two function definitions - the first one is the `add` function that has the parameter `a` and the second one is the function that has the parameter `b` which is returned by the `add` function.

Let's first look at how to compile the `add` function. This function takes in one parameter `a` and returns a function that captures that value `a`. To represent a function value that captures values we use `struct Function`, a struct that stores a pointer function and a pointer to a struct with the captured values. With `struct Function`, the body of `add` just needs to construct a `struct Function` with a pointer to the function which takes in the `b` parameter and constructs the captures struct which will store `a`, as seen below. 

```C
struct Function {
  void *function;
  void *captures;
};

struct Natural_Add_Captures {
  void *a;
};

struct Function *natural_add_first_argument(void *a) {
  struct Function *function = malloc(sizeof(struct Function));
  function->function = /* function pointer to `natural_add_second_argument` */;

  struct Natural_Add_Captures *captures = malloc(sizeof(struct Natural_Add_Captures));
  captures->a = a;

  function->captures = captures;

  return function;
}
```

Now let's look at how to compile the function that has the parameter `b`, or as it's called in the example above `natural_add_second_argument`. This function will need to take two parameters - one for the parameter `b` and another for the captures struct. Then, to provide the body of the function access to `a` it will need to read it from the captures struct, as seen below. 

```C
void *natural_add_second_argument(void *b, 
                                  struct Natural_Add_Captures *captures) {
  void *a = captures->a;
  void *result = /* add `a` and `b`*/;
  return result;
}
```

### `match` 

Now let's look at how to compile the `(* ignored *)` portion of the `add` function, or the `/* add a and b */` in `natural_add_second_argument`: 

```Coq
7  match a with
8  | Zero => b
9  | Successor (n : Natural) => Successor (add n b).
```

`match` statements correspond to `switch` statements in C. When `match`ing on a value we `switch` on the values `tag`. Then, each `case` in the `switch` statement can cast the scrutinee to the correct struct type, extract the data within the struct, and generate the code that corresponds to the Coq code after the `=>` in the `match` expression. So, our `natural_add_second_argument` function will look like this:

```C
void *natural_add_second_argument(void *b, 
                                  struct Natural_Add_Captures *captures) {
  struct Inductive *inductive = captures->a;
  void *result = NULL;

  void *match_expression_result = NULL;
  switch (inductive->tag) {
  case 0: // inductive->tag == 0
    struct Natural_Zero *zero = (struct Natural_Zero *) inductive;
    match_expression_result = /* b */;
    break;
  case 1: // inductive->tag == 1
    struct Natural_Successor *successor = (struct Natural_Successor *) inductive;
    struct Natural *n = successor->successor;

    match_expression_result = /* Successor (add n b) */;
    break;
  default:
    assert(false);
  }
  result = match_expression_result;

  return result;
}
```

### DeBruijn Indexes

To fill in the body of the arms in our `match expression` - the `/* b */` and `/* Successor (add n b) */` - we'll need to reference DeBruijn indexes, as we learned in the [second blog post](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5#debruijn-indexes). In C referencing a DeBruijn index is simple, we just use the name. For example, the arm of the `Zero` branch will look like this in C:

```C
  case 0:
    struct Natural_Zero *zero = (struct Natural_Zero *)a;
    match_expression_result = b;
    break;
```

But, when working with LLVM IR things are a bit more complicated. In particular, when referencing captured variables (like `a`) and recursive functions (like `add`). Since this blog post isn't focusing on how to compile to LLVM IR I won't go into any more detail here, but I did want to mention that compiling DeBruijn indexes to LLVM IR isn't as straightforward as it is in C. 

### Function Call

To generate code for function calls we will need to simplify the C functions that we generate. So, far we've generate four C functions - `natural_zero`, `natural_successor`, `natural_add_first_argument`, `natural_add_second_argument`. These C functions have 0, 1, 1, and 2 parameters respectively. The maximum number of parameters a function can have is 2 - one for the parameter to the equivalent Coq function and another for the struct that holds all of the values that the function captures. To simplify the code we generate to call functions I chose to make every C function take 2 parameters. If a function wouldn't have had a first parameter, then simply pass a `NULL` value as the first argument, and if a function wouldn't have had a second parameter simply pass a pointer to an empty struct as the second argument. 

With this simplification we can now generate the code for the arms of the `inductive->tag == 1` branch in `natural_add_second_argument`:

```C
case 1: // inductive->tag == 1
  struct Natural_Successor *successor = (struct Natural_Successor *) inductive;
  struct Natural *n = successor->successor;

  struct Function *add_function_a = natural_add_first_argument(n);
  void *add_result = add_function_a->function(b, add_function_a->captures);

  match_expression_result = (void *) natural_successor(add_result);
  break;
```

We first call the `natural_add_first_argument` function with the argument `n` to obtain a `struct Function` that has a reference to `natural_add_second_argument`. Then, we call `natural_add_second_argument` via `add_function_a->function` and pass `b` as the first parameter and the captures struct `add_function_a->captures` as the second parameter. This computes the `(add n b)` in `Successor (add n b)`. So, to complete the compilation of this arm we just need to call `natural_successor` with the value that `(add n b)` returned, `add_result`. 

### `add`ition

Here is all of the code put together:

```C
struct Inductive {
  uint8_t tag;
};

struct Natural_Zero {
  uint8_t tag;
};

struct Natural_Successor {
  uint8_t tag;
  void *successor;
};

struct Natural_Zero *natural_zero() {
  struct Natural_Zero *constructor = malloc(sizeof(struct Natural_Zero));
  constructor->tag = 0;
  return constructor;
}

struct Natural_Successor *natural_successor(struct Natural *natural) {
  struct Natural_Successor *constructor = malloc(sizeof(struct Natural_Successor));
  constructor->tag = 1;
  constructor->successor = natural;
  return constructor;
}

struct Function {
  void *function;
  void *captures;
};

struct Natural_Add_Captures {
  void *a;
};

void *natural_add_second_argument(void *b, 
                                  struct Natural_Add_Captures *captures) {
  struct Inductive *inductive = captures->a;
  void *result = NULL;

  void *match_expression_result = NULL;
  switch (inductive->tag) {
  case 0: // inductive->tag == 0
    struct Natural_Zero *zero = (struct Natural_Zero *) inductive;
    match_expression_result = b;
    break;
  case 1: // inductive->tag == 1
    struct Natural_Successor *successor = (struct Natural_Successor *) inductive;
    struct Natural *n = successor->successor;

    struct Function *add_function_a = natural_add_first_argument(n);
    void *add_result = add_function_a->function(b, add_function_a->captures);

    match_expression_result = (void *) natural_successor(add_result);
  break;
  default:
    assert(false);
  }
  result = match_expression_result;

  return result;
}

struct Function *natural_add_first_argument(void *a) {
  struct Function *function = malloc(sizeof(struct Function));
  function->function = (void *) natural_add_second_argument;

  struct Natural_Add_Captures *captures = malloc(sizeof(struct Natural_Add_Captures));
  captures->a = a;

  function->captures = captures;

  return function;
}
```

## What about types?

You may have wondered why I haven't discussed dependent types, sorts, or CoIC types altogether. Well, they just **are not relevant to compilation**. The code that is given to the `codegen` module has already type checked, so we can assume that it is well-formed for our purposes. In place of emitting type information, we can use void pointers and cast values to the correct type where we need them in `match` expressions. 

## Conclusion

Hopefully, by now you have a good idea of how I went about compiling the CoIC. Next, I'll reflect on my experience working on this project and wrap up this series of blog posts.

##

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 5 - Reflections](https://gist.github.com/justinfargnoli/b8837284d9ef53f578405976260b9330) ------- Previous post: [Part 3 - Type Checking](https://gist.github.com/justinfargnoli/8ded6d3c94bcfa82503ffd329460fd75)