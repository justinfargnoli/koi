# Understanding Coq - Part 5 - Reflections

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Previous post: [Part 4 - Compilation](https://gist.github.com/justinfargnoli/1ee56d4f9904176b1ea26dffee3b1d24) 

##

## Reflections

My motivation behind doing this project was to get a better understanding of how to use theorem provers. To this end, I thought that a good way to go about this would be to get a better understanding of the foundation of a theorem provers, their type system, the Calculus of Inductive Constructions (CoIC).

As I reflect on the project, I'm not sure I accomplish what I originally set out to do. I do feel like I have a much stronger understanding of the CoIC. I learned about dependent types, the `Prop` type, and type universes among many other things. But, on the other hand, my understanding of how to use theorem provers, has not advanced as much as I would have hoped. 

I now realize that working with theorem provers is a challenge, closely related to understanding the CoIC, but distinct in its own right. Working with theorem provers involves using tactics, being familiar with proof automation mechanism, defining structures in a way that is amenable to proving properties about it, and ultimately writing proofs. 

## What did I accomplish?

* I implemented a [type checker](https://github.com/justinfargnoli/koi/blob/master/compiler/src/typ.rs) and [compiler](https://github.com/justinfargnoli/koi/tree/master/compiler/src/codegen) for the CoIC. My definition of the abstract syntax tree (AST) for the CoIC is here. I tested my implementation of these [examples](https://github.com/justinfargnoli/koi/blob/master/compiler/src/hir/examples.rs).
* I wrote this series of blog posts.
* I gave multiple talks at the University of Rochester's Computer Science Department's (URCS) Systems Seminar (This seminar is attended by the systems faculty and PhD students of URCS).

## What's next for the project?

1. Fix a bug in the type checking code. Currently some test cases are failing because the type checker is doing a direct equality comparison of some type. This incorrectly fails what the two types use different DeBruijn indexes, but the DeBruijn index refer to things that are the same type. 
2. Write a parser or take as input Coq ASTs. At the moment, all of my test cases are hand written ASTs.
3. Write more test cases to ensure the robustness of the type checker and compiler. Currently the type checker and compiler both seems to be working effectively. But they are too couple to the current set of test cases. By adding more test cases I hope to expose some of the small mistakes or assumptions I made along the way that are incorrect.
4. Add the ability to compile equality checks to enhance my ability to write unit tests for the compiler. Currently, I'm testing the compiler by ensuring that LLVM IR it generates can be verified by LLVM, compiled with `clang`, and run without throwing a signal. In my eyes, this is clearly insufficient and needs to be enhanced. 

## Acknowledgements

* [MetaCoq Project](https://hal.inria.fr/hal-02167423/document)
  * The MetaCoq project formalized the Coq system and proves correctness properties about it. This particular paper describes Coq and the CoIC in great detail. I based my entire implemented of the CoIC AST and type checker on this paper, so I owe the authors a big thanks! 
* [The Calculus of Inductive Constructions](https://hal.inria.fr/hal-01094195/document)
  * This paper was the first great introductory resource that I found on the CoIC. If you aren't a subject matter expert and are interested in getting a better understanding of what the CoIC is and how it creates the Coq system, then I highly recommend this paper!

## Connect with Me

* [Twitter](https://twitter.com/justin_fargnoli)
* [LinkedIn](https://www.linkedin.com/in/justin-fargnoli/)
* [GitHub](http://github.com/justinfargnoli/)

##

[Outline](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) ------- Previous post: [Part 4 - Compilation](https://gist.github.com/justinfargnoli/1ee56d4f9904176b1ea26dffee3b1d24)