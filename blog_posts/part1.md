# Understanding Coq - Part 1 - Motivation

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 2 - The Calculus of Inductive Constructions](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5) ------- Previous post: [Part O - Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf)

##

This blog post is intended to describe what theorem provers are, show some interesting use cases of them in the real world, introduce the Calculus of Inductive Constructions, and, finally, describe what this series of blog posts *is* about and what it is *not* about. 

## Table of Contents

- [Understanding Coq - Part 1 - Motivation](#understanding-coq---part-1---motivation)
  - [Table of Contents](#table-of-contents)
  - [What is a Theorem Prover?](#what-is-a-theorem-prover)
  - [How do you use a Theorem Prover?](#how-do-you-use-a-theorem-prover)
  - [Uses of Theorem Provers in the Real World](#uses-of-theorem-provers-in-the-real-world)
    - [CompCert (Coq)](#compcert-coq)
    - [seL4 (Isabelle)](#sel4-isabelle)
    - [`mathlib` (Lean)](#mathlib-lean)
    - [Verified Software Toolchain (Coq)](#verified-software-toolchain-coq)
  - [Why would you use a Theorem Prover?](#why-would-you-use-a-theorem-prover)
    - [Trusted Theory Base](#trusted-theory-base)
  - [The Calculus of Inductive Constructions (CoIC)](#the-calculus-of-inductive-constructions-coic)
  - [What are these blog posts *not* about?](#what-are-these-blog-posts-not-about)
  - [What *are* these blog posts about?](#what-are-these-blog-posts-about)

## What is a Theorem Prover?

A theorem prover is a programming language that enables a programmer to state and prover theorem. Some examples of theorem provers are:

* [Coq](https://coq.inria.fr)
* [Lean](https://leanprover.github.io)
* [F*](https://www.fstar-lang.org)
* [Isabelle](https://isabelle.in.tum.de)

My project focuses on Coq simply because the most useful resources I found were about Coq. 

## How do you use a Theorem Prover?

To get a brief look at how programmers use theorem provers copy and paste the following code snippet into [jsCoq](https://jscoq.github.io/scratchpad.html). 

```Coq
Inductive Natural : Set :=
| Zero : Natural
| Successor (n : Natural) : Natural.

Fixpoint add (a b : Natural) : Natural :=
match a with
| Zero => b
| Successor n => Successor (add n b)
end.

Theorem plus_identity : forall a b : Natural, 
  a = b -> (add a a = add b b).
Proof.
  intros a b H.
  rewrite -> H.
  reflexivity.
Qed.
```

Press the green down arrow in the top left corner of the right-hand side panel *two* times to move the Coq interpreter's cursor to the spot after `Fixpoint add ...`, but before the line `Theorem plus_identity ...`. At this point, Coq, has read in our definition of the type `Natural` that represents the natural numbers and our function `add` that defines addition over our representation of the natural numbers. Feel free to ignore this code for now. We'll take a deeper look at it in the next blog post. 

Next, click the green down arrow *two* more times to move the Coq interpreter's cursor to the spot after `Proof.`, but before the line `intros a b H`. The line `Theorem plus_identity : forall a b : Natural, a = b -> (add a a = add b b).` defined a theorem named `plus_identity`. `plus_identity` states that if two natural numbers, `a` and `b`, are equal, then `a + a` must equal `b + b`. The `Proof` command told Coq the enter proof mode. In proof mode, Coq programmers use tactics instead of regular Coq code to prove a theorem. Tactics are programs written in the internals of the Coq system that emits Coq code. They are basically very powerful macros. `plus_identity` uses three tactics `intros`, `rewrite`, and `reflectivity`. Clicking the green down and up arrow will execute the tactics and move you through the proof of `plus_identity`. As you move Coq's cursor through the proof of `plus_identity` you can see the proof state being modified by the tactics on the right-hand side panel. Moving Coq's cursor past the `Qed` command completes the proof of the theorem and takes Coq out of proof mode. The cursor won't go past the `Qed` command if the theorem hasn't actually been proven. 

## Uses of Theorem Provers in the Real World

Below are some projects that illustrate the power and potential of theorem provers. 

### CompCert (Coq)

[CompCert](https://compcert.org) is an optimizing C compiler written in Coq that is formally verified to emit assembly code that has the same semantics as the input C code. In other words, CompCert won't miscompile C code.

### seL4 (Isabelle)

[seL4](https://sel4.systems) is a high-performance micro-kernel implemented in Isabelle. seL4 ensures that different applications running on the system are *isolated* from one another. So, if one application running on seL4 is compromised, it can be, "contained and prevented from harming other, potentially more critical parts of the system" (CITATION). 

A cool use of seL4 is detailed in the ACM article, [Formally Verified Software in the Real World](https://cacm.acm.org/magazines/2018/10/231372-formally-verified-software-in-the-real-world/fulltext). 

### `mathlib` (Lean)

[`mathlib`](https://leanprover-community.github.io), "is a community-driven effort to build a unified library of mathematics formalized in the Lean proof assistant" (CITATION). 

### Verified Software Toolchain (Coq)

The [Verified Software Toolchain](https://softwarefoundations.cis.upenn.edu/vc-current/index.html) (VST) is a toolchain that enables programmers to state and prove correctness properties about C code in Coq. This means that using the VST you can write a super fast and funky C program, but then use Coq to define what it means for the program to be correct and prove that the C program meets that correctness specification. 

## Why would you use a Theorem Prover?

Let's take a step back and think about what theorem provers buy us as software engineers.

### Trusted Theory Base

Fundamentally, using a theorem prover enables you to move from a [trusted computing base](https://en.wikipedia.org/wiki/Trusted_computing_base) to a ***trusted theory base***. If a programmer uses a theorem prover to specify what it means for their program to be correct and then uses a tool like the Verified Software Toolchain to verify that their implementation meets their correctness specification, then they no longer need to trust that their implementation is correct. They *only* need to trust that their correctness specification is correct. 

Take CompCert as an example. Without using CompCert, C programmers need to trust that their C compiler is correct. Modern optimizing C compilers, like Clang and GCC, are composed of millions of lines of C++ code and contain many bugs. A security-conscious C program might determine that, for their applications, it is not reasonable to assume that these bugs won't affect the security guarantees of their program. To alleviate this concern they can use the CompCert C compiler because CompCert was proven to output assembly code that has the exact same semantics as the C code it's given. Perhaps CompCert's correctness specification is stated incorrectly or our theorem prover has a bug, but it is much easier to audit this trusted theory base, than the many million lines of C++ trusted computing base. 

## The Calculus of Inductive Constructions (CoIC)

The type system that powers Coq and other theorem provers is the Calculus of Inductive Constructions (CoIC). The Calculus of Constructions (CoC) defines a concise functional programming language. The CoIC extends the CoC with inductive type definitions. We'll dig into this more in the next blog post, [The Calculus of Inductive Constructions](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5). 

The CoIC type system is what gives Coq and other theorem provers the power to state and prove theorems. It, in some sense, is the thing that powers these magic black boxes.

## What are these blog posts *not* about?

This series of blog posts is not about how to use Coq and other theorem provers to state and prove theorems. 

## What *are* these blog posts about?

This series of blog posts is about understanding the core of Coq and other theorem provers, the Calculus of Inductive Constructions. 

In the next blog, we'll get a first look at Coq code and some of the interesting things it can express because of the CoIC. In the third blog post, we'll look at how I went about implementing a type checker for the CoIC. In the fourth blog post, we'll look at how I went about implementing a compiler for the CoIC. Finally, in the fifth blog post, I'll reflect on my experience and summarize the state of my project. 

##

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 2 - The Calculus of Inductive Constructions](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5) ------- Previous post: [Part O - Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf)
