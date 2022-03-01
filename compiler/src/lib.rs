pub mod codegen;
pub mod erase;
pub mod hir;
pub mod parse;
pub mod typ;

// TODO: Termination checking

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
