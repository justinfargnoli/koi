# Understanding Coq - Part 1 - Motivation

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 2 - The Calculus of Inductive Constructions](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5) ------- Previous post: [Part O - Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf)

##

## Why did I do this project?

In my sophomore year at University of Rochester I took a class that taught us how to use the Coq theorem prover using the book, [Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html). I was enamored by the strong correctness properties that theorem provers enabled me to prover about my code. But, I always felt like I was working with a magic black box. I would use different combinations of tactics and, through educated guesses and lots of trial and error, prove a theorem. I was unsatisfied. I wanted to understand how theorem provers actually worked. I wanted to understand the magic black box. So, I thought the best way to try to understand Coq would be to implement Coq. That birthed this project. 

This blog post is intended to motivate why theorem provers are interesting and powerful programming languages. I'll then introduce what the Calculus of Inductive Constructions is and, finally, describe what these blog posts *are* about and what they are *not* about. 

## Table of Contents

- [Understanding Coq - Part 1 - Motivation](#understanding-coq---part-1---motivation)
  - [Why did I do this project?](#why-did-i-do-this-project)
  - [Table of Contents](#table-of-contents)
  - [What is a Theorem Prover?](#what-is-a-theorem-prover)
  - [How do you use a Theorem Prover?](#how-do-you-use-a-theorem-prover)
  - [Uses of Theorem Provers in the Real World](#uses-of-theorem-provers-in-the-real-world)
    - [CompCert (Coq)](#compcert-coq)
    - [seL4 (Isabelle)](#sel4-isabelle)
    - [Xena Project (Lean)](#xena-project-lean)
    - [Verified Software Toolchain (Coq)](#verified-software-toolchain-coq)
  - [Why would you a Theorem Prover?](#why-would-you-a-theorem-prover)
    - [Trusted Theory Base](#trusted-theory-base)
  - [The Calculus of Inductive Constructions (CoIC)](#the-calculus-of-inductive-constructions-coic)
  - [What are these blog posts *not* about?](#what-are-these-blog-posts-not-about)
  - [What *are* these blog posts about?](#what-are-these-blog-posts-about)
  - [Accompanying Materials](#accompanying-materials)
    - [Code](#code)
    - [Talk](#talk)

## What is a Theorem Prover?

A theorem prover is a programming language that enables a programer to state and prover theorem. Some examples of theorem provers are:

* [Coq](https://coq.inria.fr)
* [Lean](https://leanprover.github.io)
* [F*](https://www.fstar-lang.org)
* [Isabelle](https://isabelle.in.tum.de)

My project focuses on Coq simply because the most useful resources I found were about Coq. 

## How do you use a Theorem Prover?

## Uses of Theorem Provers in the Real World

### CompCert (Coq)

### seL4 (Isabelle)

### Xena Project (Lean)

### Verified Software Toolchain (Coq)

## Why would you a Theorem Prover?

Let's take a step back and think about what theorem provers buy us as software engineers.

### Trusted Theory Base

Fundamentally, using a theorem prover enables you to move from a [trusted computing base](https://en.wikipedia.org/wiki/Trusted_computing_base) to a ***trusted theory base***. If a programmer uses a theorem prover to specify what it means for their program to be correct and then uses a tool like the Verified Software Toolchain to verify that their implementation meets their correctness specification, then they no longer need to trust that their implementation is correct. They *only* need to trust that their correctness specification is correct. 

Take CompCert as an example. Without using CompCert, C programmers need to trust that their C compiler is correct. Modern optimizing C compilers, like Clang and GCC, are composed of millions of lines of C++ code and contain many bugs. A security conscious C program might determine that, for their applications, it is not reasonable to assume that these bugs won't affect the security guarantees of their program. To alleviate this concern they can use the CompCert C compiler because CompCert was proved to output assembly code that has the exact same semantics as the C code it's given. Perhaps CompCert's correctness specification is state incorrectly or our theorem prover has a bug, but it is much easier to audit this trusted theory base, than the many million lines of C++ trusted computing base. 

## The Calculus of Inductive Constructions (CoIC)

## What are these blog posts *not* about?

## What *are* these blog posts about?

## Accompanying Materials

### Code

### Talk

##

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Next post: [Part 2 - The Calculus of Inductive Constructions](https://gist.github.com/justinfargnoli/900e0bd457e8eacfc842a0a154730ff5) ------- Previous post: [Part O - Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf)
