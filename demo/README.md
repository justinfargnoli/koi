# Calculus of Inductive Constructions Demo 

There are two files in Coq and Lean that demonstrate what I'd like to accomplish this semester. 

* `Main.lean` - Lean
* `Demo.v` - Coq
  * Note that I used tactics in this file. However, I want my language to only use the proof object constructed by the tactics. The proof object can be visualized with the `Print.` command. 

The Coq file can be run online on this [website](https://coq.vercel.app/scratchpad.html), and the Lean file can be run online on this [website](https://leanprover.github.io/live/latest/).

At a high level, I'd like to implement the calculus of inductive constructions. More specifically, I'd like to:

* Implement a type checker for the calculus of constructions.
* Add [inductive families](https://leanprover.github.io/lean4/doc/declarations.html#inductive-families)
  * Inductive families are a generalization of regular inductive types that theorem provers like Coq and Lean have. 
* Implement commands like Lean's `#eval`, `#check`, and `#print` to allow the user to query the system. 
* Compile it to LLVM IR

Then, optionally, (in order of priority):

* To make the language feel like a more typical programming language, I might:
  * Implement type classes
  * Implement an IO Monad
  * Implement type inference
* To make the language feel like a more typical theorem prover, I might:
  * Add a [tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html) DSL
  * Allow user-defined notation and macros

My goal for this project is to just expose the calculus of constructions and not to get bogged down implementing usability features that make working with this kind of type-systems feasible in practice like a tactics DSL and type inference. 
