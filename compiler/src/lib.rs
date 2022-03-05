pub mod codegen;
pub mod hir;
pub mod parse;
pub mod typ;

// TODO: termination checking
// TODO: make sure functions aren't named 'main'
// TODO: implement currying

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
