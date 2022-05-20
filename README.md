# koi 
(**K**alculus **O**f **I**nductive constructions)

An Approachable Implementation of a Compiler for the Calculus of Inductive Constructions.

## Blog Posts

[Here](https://gist.github.com/justinfargnoli/41ab2558183746852e8c30589a4bbbaf) is a series of blog posts that I wrote about this project.

## Build 

1. Clone this repository.
2. This project is dependent on LLVM 13. Follow the instructions in this [`README.md`](compiler/submodules/README.md) to download and build LLVM 13. 
3. Navigate to the `compiler` directory. 
4. Use `cargo` to build and test the project. 
    * `cargo check` to check that the project compiles.
    * `cargo test` to compile the project and run its tests.