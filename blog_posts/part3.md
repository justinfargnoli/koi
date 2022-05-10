# Understanding Coq - Part 3 - Type Checking

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 4 - Compilation](https://gist.github.com/justinfargnoli/1ee56d4f9904176b1ea26dffee3b1d24) ------- Previous post: [Part 2 - The Calculus of Inductive Constructions](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5)

##

In this blog post I'll walk through the approach I took to type check the Calculus of Inductive Constructions (CoIC). 

A special feature of the CoIC is that every construct in the CoIC has a type (even types themselves). So, in each subsection, I will look at how to type-check one construct of the CoIC and what the type of each language construct is.

## Table of Contents

- [Understanding Coq - Part 3 - Type Checking](#understanding-coq---part-3---type-checking)
  - [Table of Contents](#table-of-contents)
  - [Running Example](#running-example)
  - [Some Syntax](#some-syntax)
  - [Sorts](#sorts)
  - [Some Definitions](#some-definitions)
  - [Global & Local Environments](#global--local-environments)
  - [Dependent Types](#dependent-types)
  - [Inductive Types](#inductive-types)
  - [Functions](#functions)
    - [Dependent Types are Powerful](#dependent-types-are-powerful)
  - [Function Call](#function-call)
  - [Match](#match)
  - [Conclusion](#conclusion)

## Running Example

This post will use the `Vector` type and the `append` function for vectors to illustrate the type checking process. 

```Coq
1  Inductive Vector (T : Set) : Natural -> Set :=
2  | Nil : Vector T Zero
3  | Cons (head : T) 
4         (tail_length : Natural) 
5         (tail : Vector T tail_length) 
6         : Vector T (Successor tail_length). 
7  
8  Fixpoint append (T : Set) (n m : Natural) (a : Vector T n) (b : Vector T m) : Vector T (add n m) :=
9  match a with
10  | Nil (_ : Set) => b
11  | Cons (T : Set) (head : T) (tail_length : Natural) (tail : Vector T tail_length) => 
12        Cons T head (add tail_length m) (append T tail_length m tail b).
```

## Some Syntax

The following syntax `thing1 : thing2` should be read as "the type of `thing1` is `thing2`." For example, in C we could say `4.2 : float`, or the type of `4.2` is the type `float`.

## Sorts

Let's begin with one of the most basic, from a type checking perspective, language constructs, sorts. A sort is either the value `Set`, `Prop`, or `Type i` where `i` is a natural number. As we saw in the `List`, `Vector`, and `modus_ponens` example from the previous blog post, `Set` and `Prop` let us represent the type of types that are relevant to computing or proofs respectively.

Since every language construct in Coq has a type, it would make sense to ask what is the type of `Set` and `Prop` is. Well, the type of `Set` and `Prop` is, for lack of a better name, `Type 1`. Continuing this line of thinking, the type of `Type 1` is `Type 2`, the type of `Type 2` is `Type 3`, and the type of `Type n` is `Type (n + 1)`. This defines an infinite hierarchy of types having types. This concept is referred to as type universes.

Type universes have a substantial impact on the type checking process, particularly with references to global constants, inductive types, and the constructors of inductive types. However, I don't have a strong understanding of how they work. Although there are good resources to understand how to use type universes as a programmer (like [Adam Chlipala's textbook's chapter on universes](http://adam.chlipala.net/cpdt/html/Universes.html)), I struggled to find approachable resources that talked about how to implement type universes. For this reason, my type checker does not handle any of the effects that type universes have on other parts of the CoIC. 

Below are some examples:

* `Natural : Set`
* `Set : Type 1`
* `Prop : Type 1`
* `Type 1 : Type 2`
* `Type 34 : Type 35`

## Some Definitions

Before going further we need to define two terms:

* well-formed: Something is well-formed if it type checks.
* well-sorted: Something is well-sorted if it is well-formed and its type is a sort.

## Global & Local Environments 

Throughout the type checking process, we'll need a way to represent what variables and names are available to use. We accomplish this by using a global and local environment. 

The global environment stores the definition and types of inductives, their constructors, and top-level functions. With `Vector` and `append`, the global environment will store the definition of the `Vector` type, the type of all of its constructors, and the name and type of the `append` function. Whenever the type checker encounters an inductive, the constructor of an inductive, or a reference to a function declared in the global scope it uses the global environment to look up its corresponding type. 

The local environment stores the variables that go in and out of scope as the type checking algorithm traverses a particular piece of code. The local environment is implemented with a stack as seen in the example in the [DeBruijn indexes](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5#debruijn-indexes) section of the previous blog post. Whenever the type-checking algorithm encounters a DeBruijn index it uses the local environment to look up the type that corresponds to that variable.

## Dependent Types

Dependent types are the types of functions. They consist of two elements: the type of the function's parameter and the type of the function body (I'll refer to this as the functions return type.). Dependent types are sometimes called pi types, so we'll use the following syntax to describe a dependent type: `parameter-type -> return-type`.

To type check a dependent type, first, check that the parameter type is well-sorted. Then, check that the return type is well-sorted when the parameter type is in the local context. 

The type of a dependent type is a sort. In particular, it is the whichever sort, the parameter type's sort or the return type's sort, that is larger. 

There is one caveat, If the return type's sort is `Prop`, then the type of the dependent type is `Prop` regardless of what the parameter type's sort is. This is referred to as the impredicativity of `Prop`. The impredicativity of `Prop` is a very powerful concept, but one that I don't understand well, so unfortunately I'm not really able to go into any more detail. 

Below are some examples:

* `(Set -> Set) : Type 1`
* `(Set -> Set -> Set) : Type 1`
* `(Prop -> Set) : Type 1`
* `(Type 15 -> Prop) : Prop`
* `(Type 2 -> Type 3) : Type 4`

We'll see an even more interesting use of dependent types in the [Dependent Types are Powerful](#dependent-types-are-powerful) subsection.

## Inductive Types

We now have enough background to examine the `Vector` type:

```Coq
1  Inductive Vector (T : Set) : Natural -> Set :=
2  | Nil : Vector T Zero
3  | Cons (head : T) 
4         (tail_length : Natural) 
5         (tail : Vector T tail_length) 
6         : Vector T (Successor tail_length). 
```

To type check the definition of this inductive type we first ensure that the type of the inductive type is well-sorted. This syntax, `Vector (T : Set) : Natural -> Set` indicated that the type of `Vector` is `Set -> Natural -> Set`. Since `(Set -> Natural -> Set) : Type 1`, and `Type 1` is a sort, we know that `Vector`'s type is well-sorted. 

Then, we check each constructor of the inductive type is well-sorted:

* The `Nil` constructor is well sorted: `Vector T Zero : Set`
* The `Cons` constructor is well sorted: `T -> Natural -> Vector T tail_length -> Vector T (Successor tail_length) : Set`

Finally, I check that each constructor is actually constructing an instance of the inductive type it's associated with:

* The `Nil` constructor returns a `Vector` via `Vector T Zero`.
* The `Cons` constructor returns a `Vector` via `Vector T (Successor tail_length)`.

## Functions

Let's continue with our running example, `Vector`, by looking at the explicitly curried version of the `append` function.

```Coq
Fixpoint append (T : Set) := 
    fun (n : Natural) =>
    fun (m : Natural) =>
    fun (a : Vector T n) =>
    fun (b : Vector T m) => (* ignored *).
```

To type check a function we first check that the type of the parameter is well-sorted. Then, add the parameter type to the local context and type check the body. 

### Dependent Types are Powerful

The type of the append function is the following dependent type: 

```
(T : Set) -> (n : Natural) -> (m : Natural) -> 
    Vector T n -> Vector T m -> Vector T (add n m)
```

Let's take a deeper look at this type to get a better understanding of why dependent types are called *dependent* types. In particular let's zoom in on the type of the fourth parameter, `Vector T n`. 

The type `Vector T n` references two other parameters in its type - the first parameter `T : Set` and the second parameter `n : Natural`. This means that the *type* of the fourth parameter is dependent on the *values* passed as the first and second parameters. So, if you call the `append` function like so `append Natural Zero ...`, then the type of the fourth parameter to `append` must be `Vector Natural Zero`. The ability for types to depend on values is a very powerful concept and is something that the CoIC has that regular programming languages don't.

## Function Call

To type check a function call we check that:

* The function is well-formed.
* The type of the function is well-sorted.
* The argument is well-formed.
* The type of the function's parameter is equivalent to the type of the argument. 

The type of a function call is the return type of the function. 

For example, let's look at `((((append T) tail_length) m) tail) b`. 

* `append : (T : Set) -> (n : Natural) -> (m : Natural) -> Vector T n -> Vector T m -> Vector T (add n m)`
* `(append T) : (n : Natural) -> (m : Natural) -> Vector T n -> Vector T m -> Vector T (add n m)`
* `((append T) tail_length) : (m : Natural) -> Vector T tail_length -> Vector T m -> Vector T (add tail_length m)`
* `(((append T) tail_length) m) : Vector T tail_length -> Vector T m -> Vector T (add tail_length m)`
* `((((append T) tail_length) m) tail) : Vector T m -> Vector T (add tail_length m)`
* `(((((append T) tail_length) m) tail) b) : Vector T (add tail_length m)`

Notice how `Vector T n` from the second bullet point becomes `Vector T tail_length` in the second bullet point. This reflects the fact that we now know that `n` must be `tail_length`. 

Function calls, or as their sometimes otherwise called, function applications, or just applications are also used to represent expressions `Vector T n`. Recall from earlier that inductive types can have parameters. To apply an argument to those parameters you use an application expression. Let's look at how the type of `Vector T n` changes as we apply arguments to it:

* `Vector : Set -> Natural -> Set`
* `Vector T : Natural -> Set`
* `Vector T n : Set`

## Match 

A side note about my implementation: Coq has lots of automation all throughout the system to make working with the CoIC easier. One place you can see this is in the syntax for `match` statements. As we'll see below, we need to know the name of the inductive type that the scrutinee is and the return type of the `match` expression to type check the `match` expression. Coq automatically infers these things and gives the information to the type checker. My implementation does not, so all of the information must be explicitly written out. 

To type check a `match` expression we check that:

* The scrutinee's inductive type is declared in the global environment.
* The type of the scrutinee is equivalent to that inductive type.
* The type that the `match` expression returns is well-formed.
* The return type of each branch of the `match` is equivalent to the return type of the `match` expression.
  
The type of the `match` expression is the stated return type of the expression. 

Let's walk through type checking the `match` expression in the `append` function.

```Coq 
Fixpoint append (T : Set) (n m : Natural) (a : Vector T n) (b : Vector T m) : Vector T (add n m) :=
match a with
 | Nil (_ : Set) => b
 | Cons (T : Set) (head : T) (tail_length : Natural) (tail : Vector T tail_length) => 
       Cons T head (add tail_length m) (append T tail_length m tail b).
```

First, we check that `a`'s inductive type, `Vector`, is declared in the global environment. Since the declaration of the `Vector` appears before `append` in the [Running Example](#running-example) subsection this check will pass. Then, we check that `a` is in fact a `Vector`. This can be checked by looking up `a` in the local environment and seeing that its type is `Vector T n`. Next, we check that `Vector T (add n m)` is well-formed, which it is. Finally, we check that the return type of each branch is equivalent to the stated return type of the `match` expression. The return type of the `Nil` arm is `Vector T m`. Coq's simplification engine can see that `Vector T m` and `Vector T (add 0 m)` are equivalent types because `(add 0 m)` is equivalent to `m`. The return type of the `Cons` branch is `Vector T (Successor (add tail_length m))`. Similarly to the `Nil` branch, Coq's simplification engine can see that `Vector T (Successor (add tail_length m))` and `Vector T (add n m)` are equivalent because `n` is equivalent to `Successor tail_length` and `1 + (tail_length + m) = n + m` when `n := 1 + tail_length`.

## Conclusion

Hopefully, by now you feel like you have a good idea of what it looks like to type checking the CoIC. Next, we'll look at how I went about compiling the CoIC.

##

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 4 - Compilation](https://gist.github.com/justinfargnoli/1ee56d4f9904176b1ea26dffee3b1d24) ------- Previous post: [Part 2 - The Calculus of Inductive Constructions](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5)