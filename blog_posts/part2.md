# Understanding Coq - Part 2 - The Calculus of Inductive Constructions

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 3 - Type Checking](https://gist.github.com/justinfargnoli/8ded6d3c94bcfa82503ffd329460fd75) ------- Previous post: [Part 1 - Motivation]([googl.com](https://gist.github.com/justinfargnoli/2c0b67da779ecfe7c47bce494c9dff38))

##

In this blog post, I want to walk through four examples of Coq code and explain what's going on. My goal is to introduce Coq syntax and show some of the power of the Calculus of Inductive Construction. Two of these code snippets, [`Natural` Number](#natural-number) and [`Vector`](#vector), will be running examples used in the next two blog posts which will focus on type checking and compilation respectively.

## Table of Contents

- [Understanding Coq - Part 2 - The Calculus of Inductive Constructions](#understanding-coq---part-2---the-calculus-of-inductive-constructions)
  - [Table of Contents](#table-of-contents)
  - [`List`](#list)
    - [The `List` Type](#the-list-type)
      - [Inductive Types](#inductive-types)
      - [`Set`](#set)
    - [Appending `List`s](#appending-lists)
      - [`Fixpoint`](#fixpoint)
      - [Function Application](#function-application)
      - [Weird Constructor Syntax](#weird-constructor-syntax)
  - [`Natural` Number](#natural-number)
    - [`Natural` Number Type](#natural-number-type)
    - [Adding `Natural` Numbers](#adding-natural-numbers)
      - [Function Currying](#function-currying)
      - [DeBruijn Indexes](#debruijn-indexes)
  - [`Vector`](#vector)
    - [`Vector` Type](#vector-type)
      - [Inductive Type Families](#inductive-type-families)
    - [Appending `Vector`s](#appending-vectors)
  - [Modus Ponens](#modus-ponens)
    - [`Prop`](#prop)
  - [Conclusion](#conclusion)
  - [](#)

## `List`

Our first example is a run-of-the-mill functional list.

### The `List` Type 

```Coq
1  Inductive List (T : Set) : Set :=
2  | Nil : List T
3  | Cons (head : T) (tail : List T) : List T. 
```

Let's read through this code line by line:

* On line 1 we declare an inductive type named `List`. `(T : Set)` says that our `List` type takes in one parameter named `T` of type `Set`. The trailing `: Set` says that the type of our inductive type `List` is the type `Set`.  
* On line 2 we declare a constructor named `Nil` for our inductive type. The `Nil` constructor doesn't have any parameters. It simply returns the type `List T`.
* On line 3 we declare a constructor named `Cons` for our inductive type. The `Cons` constructor has two parameters - one named `head` of type `T` and another named `tail` of type `List T`. The type returned by the `Cons` constructor is `List T`.

#### Inductive Types

Above I said that `List` is an inductive type, but what is an inductive type? Inductive types are similar to [algebraic data types](https://en.wikipedia.org/wiki/Algebraic_data_type) - for example Rust `enum`s, Haskell `data`, and OCaml `type`s. They can have 0 to n parameters, 0 to n constructors and each constructor can have 0 to n parameters. When you call a constructor and pass it its arguments, it will return to you an instance of the inductive type. 

Let's connect this back to the `List` type. When we call the `Nil` constructor, we'll get an instance of the `List` type. When we call the `Cons` constructor and pass it two arguments - one of type `T` and another of type `List T` - we'll also get an instance of the `List` type. These two constructors are the only way we can construct an instance of the `List` type. 

#### `Set`

When looking at the `List` type I said that the type of `List` is `Set`, but what is `Set`? `Set` is the type of types. This probably sounds kind of confusing right now because in ordinary programming languages our types don't have types, but in Coq they do! This is one of the ways that Coq is more expressive than your ordinary programming language. A simple way to think about `Set` is to relate it to programming with generics:

```Java
class LinkedList<T> {
    T data;
    LinkedList<T> next;
}
```
Above is a snippet of Java code. It's a linked list that's generic over the type `T`. If this were Coq code we would say that the type of `T` is the type `Set` because `Set` is the type of types.

Going back to our definition of the `List` type, we see that `List` is parameterized by `(T : Set)`. This is Coq's way of saying that `List` is generic over the type `T`, just like how in Java we said that the `LinkedList` class is generic over the type `T`. So, we can pass any type whose type is `Set`, like our `List` type or our `Natural` number type that we'll look at next, to specify that a `List` is generic over that type. For example, `List Natural` would be the type of a list of natural numbers and `List (List Natural)` would be the type of a list of lists of natural numbers. `Natural` and `(List Natural)` are both valid arguments for the `T` parameter on the `List` type because the type of both `Natural` and `List` is `Set`!

It's important to note that the type of `Set` is **NOT** `Set`. It's actually `Type 1`. I'll elaborate on this more in the next blog post on type checking. 

### Appending `List`s

```Coq
4  Fixpoint append (T : Set) (a b : List T) : List T :=
5  match a with
6  | Nil (_ : Set) => b
7  | Cons (T : Set) (head : T) (tail : List T) => Cons T head (append T tail b).
```

`append` is a function that takes in three parameters, the latter two, `a` and `b`, are both of type `List T`. (In other words, `a` and `b` are both lists and the data that those lists hold are of the same type.) The body of the function `match`es on `a`. The `match` statement says that if `a`, the scrutinee of the `match` expression, was constructed with the `Nil` constructor, then return `b`, but if it was constructed with the `Cons` constructor, then construct a new list whose `head` is the `head` of the list `a` and whose `tail` is the result of `append`ing `b` to `a`'s `tail`.

#### `Fixpoint`
Our `append` function is declared with the `Fixpoint` keyword. This tells Coq that `append` is a recursive function. Recursive functions in Coq must terminate to ensure that Coq is logically consistent. Coq uses conservative syntactic checks to verify that a `Fixpoint` function does in fact terminate. 

#### Function Application

To understand how functions are called in Coq, let's examine `(append T tail b)` on line 7. Here we're calling the `append` function declared on line 4 and are passing the `T` declared on line 7 as the first argument, the `tail` declared on line 7 as the second argument, and the parameter `b` as the third argument.

#### Weird Constructor Syntax

The syntax for working with constructors is kind of funky, so let's break down line 7 to get a better understanding of how they work. After the `=>` on line 7, we call the `Cons` constructors and pass three arguments `T`, `head`, and `(append T tail b)` to it. You might ask yourself, why are we passing three arguments to `Cons` when in its definition on line 3 only took 2 parameters? Well if you recall, the type `List` took a parameter `(T : Set)`. That parameter `T` applies to all constructors of the `List` type. So, both the `Nil` and `Cons` constructor implicitly have `(T : Set)` as their first parameter.

Taking this into account, we know that the type of the `Cons` constructor is a function that has takes the following three parameters `T : Set`, `head : T`, and `tail : List T` and returns a value of type `List T`. Thus, when calling `Cons` we have to make sure we pass three arguments. 

## `Natural` Number

Now let's look at one way to represent natural numbers in Coq. 

### `Natural` Number Type

```Coq
1  Inductive Natural : Set :=
2  | Zero : Natural
3  | Successor (n : Natural) : Natural. 
```

Above we've defined an inductive type  `Natural` with two constructors. The first constructor `Zero` doesn't have any parameters. It represents the natural number 0. The second constructor `Successor` has one parameter, another natural number `n`. Calling the `Successor` constructor with some natural number `n` as an argument represents computing `n + 1`. 

So with this representation of the natural number, we can construct the number 1 by applying the `Successor` constructor to the `Zero` constructor like so `Successor Zero` (i.e. `1 + 0` gives us the number 1). Similarly, we can construct the number 3 with the following code `Successor (Successor (Successor Zero))` (i.e. `1 + (1 + (1 + 0))` gives us 3).

Remember that this is just one way you can go about representing the natural numbers in Coq, and isn't necessarily the best way for all applications. Performance critical code would suffer from this representation, while a programer proving the commutativity of addition would benefit from this representation's simple structure. 

### Adding `Natural` Numbers

```Coq
4  Fixpoint add (a b : Natural) : Natural :=
5  match a with
6  | Zero => b
7  | Successor (n : Natural) => Successor (add n b).
```

Above is a definition of addition over the representation of natural numbers we defined on lines 1-3. `add` is a recursive function that takes in two parameters `a` and `b`. If `a` is 0, then you return b. From a mathematical perspective, line 7 says that when `a = 1 + n` return `1 + (n + b)` (This makes sense because `1 + (n + b) = a + b` when `a = 1 + n`). From a computational perspective, line 7 is unwrapping all of the `Successor`s on `a` and putting them onto `b`. 

#### Function Currying

In Coq function are [curried](https://stackoverflow.com/questions/36314/what-is-currying). This means that functions in Coq actually only take in one parameter. When we declared the `add` function above, Coq transformed it into the function below.

```Coq
8  Fixpoint add (a : Natural) : Natural -> Natural :=
9      fun (b : Natural) =>
10         match a with
11         | Zero => b
12         | Successor (n : Natural) => Successor (add n b).
```

In this form, we can see that our `add` function only has one parameter `a` and its body just returns a function that takes our other parameter `b`. 

Function currying enables us to call our `add` function with only some of its arguments. For example, if we called `add` with just the argument `3`, like so `add 3`, then we would get a function that will take a `Natural` number and add it with 3. 

#### DeBruijn Indexes

[DeBruijn indexes](https://en.wikipedia.org/wiki/De_Bruijn_index) are a way of representing the use of local variables within a compiler. Instead of working with the string representation of variables - `add`, `a`, `b`, and `n` - we can use integers to index the specific variables that we want. This means we don't have to deal with naming conflicts of ambiguity in our type checker or when doing code generation. 

When learning about DeBruijn indexes it's helpful to think about them as indexing into a stack. We push a variable onto the stack when its local scope begins and pop it from the stack when it ends. Then, when we reference the name we use an integer, or DeBruijn index, to specify how far down the stack the variable currently is. 

|Before `add`|After `add` & Before `a`|After `a` & Before `b`|After `b` & Before `match` Branches|Body of `Zero` Branch|Body of `Successor` Branch|
|---|---|---|---|---|---|
||||||`n`: index 0|
||||`b`: index 0|`b`: index 0|`b`: index 1|
|||`a`: index 0|`a`: index 1|`a`: index 1|`a`: index 2|
|*empty stack*|`add`: index 0|`add`: index 1|`add`: index 2|`add`: index 2|`add`: index 3|

Above is a table that shows the state of the stack as we traverse the `add` function. Below is what the `add` function looks like when using DeBruijn indexes instead of names. 

```Coq
13  Fixpoint add (a : Natural) : Natural -> Natural :=
14      fun (b : Natural) :=
15          match 1 with
16          | Zero => 0
17          | Successor (n : Natural) => Successor (3 0 1).
```

On line 15 we use the DeBruijn index `1` to index the variable `a` because the variable `a` will be 1 element down the stack after `b`'s scope has begun but before the branches of the `match` statement. To access `b` on line 16 we use the DeBruijn index `0` because `b` will be at the top of the stack. Finally, we replace `(add n b)` with `(3 0 1)` because `add` will be at the bottom of the stack, `n` will be at the top of the stack, and `b` will be one element down the stack. 

## `Vector`

Next, let's look at the `Vector` type. The `Vector` type is identical to the `List` type that we saw earlier with one exception, the `Vector` type stores its length in its type. This means that a `Vector` of length 5 and a `Vector` of length 10 are *different* types. 

### `Vector` Type

```Coq
1  Inductive Vector (T : Set) : Natural -> Set :=
2  | Nil : Vector T Zero
3  | Cons (head : T) 
4         (tail_length : Natural) 
5         (tail : Vector T tail_length) 
6         : Vector T (Successor tail_length). 
```

Like the `List` type, `Vector` has two constructors `Nil` and `Cons`. The `Nil` constructor returns a `Vector` that's generic over `T` and has a length `Zero`: `Vector T Zero`. The `Cons` constructor takes in three parameters - the head of the list, the length of the tail, and the tail of the list. It then returns a `Vector` that's generic over `T` and is one element longer than the `tail`: `Vector T (Successor tail_length)`.

The `Cons` constructor shows some of the expressive power of Coq and the CoIC. The third parameter to `Cons`, `tail`, type is dependent on the value passed to the second parameter `tail_length`. This is an example of a [dependent type](https://en.wikipedia.org/wiki/Dependent_type), a type that is dependent on a value. Likewise, the type `Cons` returns is itself dependent on the length of the `tail`.

#### Inductive Type Families

This `Vector` definition isn't any old inductive type, it's a [inductive type family](https://leanprover.github.io/theorem_proving_in_lean4/inductive_types.html#inductive-families). We can see this syntactically because the second parameter to the inductive type, a `Natural` number, is written after the `:` on line 1. Being an inductive type family, the `Vector` type can define multiple types, or a family of types, in the definition of one inductive type! 

Let's break this down a bit more. The `Nil` constructor constructs a value of type `Vector T Zero`. This is one of the types in the `Vector` type family. The `Cons` constructor constructs a value of type `Vector T (Successor tail_length)`. This type is dependent on the type of tail parameter, `Vector T tail_length`. In other words, the `Cons` constructor uses a type that already belongs to the `Vector` type family, `Vector T tail_length`, to construct another type in the `Vector` type family, `Vector T (Successor tail_length)`. 

An important property of different types in a type family is that they are not equal. `Vector T Zero`, the empty `Vector`, is the same type as `Vector Type Zero`, but it is **not** the same type as `Vector Type (Successor Zero)`, a `Vector` with one element. 

This enables users to write functions that operate on a `Vector` and guarantee that they don't access an out of bounds index. An example is the `append` function shown below. It guarantees that the `Vector` it returns has a length that's the sum of the length of the `Vector`s it was passed. 

### Appending `Vector`s

```Coq
7  Fixpoint append (T : Set) (n m : Natural) (a : Vector T n) (b : Vector T m) : Vector T (add n m) :=
8  match a with
9  | Nil (_ : Set) => b
10 | Cons (T : Set) (head : T) (tail_length : Natural) (tail : Vector T tail_length) => 
11        Cons T head (add tail_length m) (append T tail_length m tail b).
```

The type of our `append` function for `Vector`s stores lots of information for us. First, it states that values that the two `Vector`s that we're appending `a` and `b` must be of the same type. Second, that `Vector`s `a` and `b` can have different lengths, `n` and `m` respectively. Lastly, the length of the `Vector` that `append` will return is the sum of the length of `a` and the length of `b`.

The body of the `append` function says that if `a` is an empty `Vector`, then return `b`, but if a is not an empty `Vector`, then construct a new `Vector` whose head is the `head` of `a` and whose tail is of length `tail_length + m` and is constructed by `append`ing `b` onto the `tail` of `a`.

## Modus Ponens

To get a brief look at the proof side of Coq let's look at a definition of the logical statement [modus ponens](https://en.wikipedia.org/wiki/Modus_ponens): if a proposition p implies the proposition q, and p is true, then q is true.

```Coq
1  Definition modus_ponens (P Q : Prop) (implication : P -> Q) (p : P) : Q := implication p.
```

Our Coq function `modus_ponens` takes in four parameters `P` and `Q` of type `Prop`, the type of proofs, a function `implication` that takes in a value of type `P` and returns a value of type `Q`, and value `p` of type `P` and returns the result of applying the function `implication` to the argument `p`.

### `Prop`

Let's dig deeper into the type `Prop`. First, I have to come clean. Earlier when I said that `Set` is the type of types. I wasn't giving you the full story. The more precise definition of `Set` is: `Set` is the type of types that are *relevant to computation*. This difference is important when comparing `Set` with `Prop`. 

`Prop` is the dual of `Set`. It also represents the type types, but in particular, `Prop` is the type of types that are *relevant to proofs*. 

So, in our `modus_ponens` function the values `P` and `Q` are any proofs that we've proved in Coq. In other words, our `modus_ponens` function is generic over all proofs. 

Similar to `Set`, the type of `Prop` is **NOT** `Prop`. It's also `Type 1`. Again, I'll elaborate on this more in the next blog post on type checking. 

## Conclusion

Hopefully, you feel like you have a better understanding of the syntax and the expressive power of Coq and the CoIC. Next, we'll look at how to go about type checking CoIC code. 

## 

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 3 - Type Checking](https://gist.github.com/justinfargnoli/8ded6d3c94bcfa82503ffd329460fd75) ------- Previous post: [Part 1 - Motivation]([googl.com](https://gist.github.com/justinfargnoli/2c0b67da779ecfe7c47bce494c9dff38))