pub mod global {
    use inkwell::{
        types::{PointerType, StructType},
        values::PointerValue,
    };

    #[derive(Debug)]
    enum Declaration<'ctx> {
        Constant {
            name: String,
            function_pointer: PointerValue<'ctx>,
        },
        Inductive(String, Inductive<'ctx>),
    }

    #[derive(Debug)]
    pub struct Inductive<'ctx> {
        pub name: String,
        pub llvm_type: PointerType<'ctx>,
        pub constructors: Vec<Constructor<'ctx>>,
    }

    #[derive(Debug)]
    pub struct Constructor<'ctx> {
        pub name: String,
        pub struct_type: StructType<'ctx>,
        pub function: Option<ConstructorFunction<'ctx>>,
    }

    #[derive(Debug, Clone)]
    pub enum ConstructorFunction<'ctx> {
        ZeroArgumentFunctionPointer(PointerValue<'ctx>),
        FunctionPointer(PointerValue<'ctx>),
    }

    #[derive(Debug)]
    pub struct Environment<'ctx> {
        declarations: Vec<Declaration<'ctx>>,
    }

    impl<'ctx> Environment<'ctx> {
        pub fn new() -> Environment<'ctx> {
            Environment {
                declarations: Vec::new(),
            }
        }

        pub fn lookup_inductive_llvm_type(&self, name: &str) -> PointerType<'ctx> {
            self.lookup_inductive(name).llvm_type
        }

        pub fn lookup_constructor_function(
            &self,
            inductive_name: &str,
            constructor_index: usize,
        ) -> ConstructorFunction<'ctx> {
            self.lookup_constructor(inductive_name, constructor_index)
                .function
                .as_ref()
                .unwrap()
                .clone()
        }

        pub fn lookup_constructor_struct_type(
            &self,
            inductive_name: &str,
            constructor_index: usize,
        ) -> StructType<'ctx> {
            self.lookup_constructor(inductive_name, constructor_index)
                .struct_type
        }

        pub fn lookup_constructor(
            &self,
            inductive_name: &str,
            constructor_index: usize,
        ) -> &Constructor<'ctx> {
            self.lookup_inductive(inductive_name)
                .constructors
                .get(constructor_index)
                .unwrap()
        }

        pub fn lookup_inductive(&self, name: &str) -> &Inductive<'ctx> {
            self.declarations
                .iter()
                .find_map(|declaration| {
                    if let Declaration::Inductive(inductive_name, inductive) = declaration {
                        if inductive_name == name {
                            return Some(inductive);
                        }
                    }
                    None
                })
                .unwrap()
        }

        fn lookup_inductive_mut(&mut self, name: &str) -> &mut Inductive<'ctx> {
            self.declarations
                .iter_mut()
                .find_map(|declaration| {
                    if let Declaration::Inductive(inductive_name, inductive) = declaration {
                        if inductive_name == name {
                            return Some(inductive);
                        }
                    }
                    None
                })
                .unwrap()
        }

        pub fn lookup_constant_value(&self, name: &str) -> PointerValue<'ctx> {
            *self
                .declarations
                .iter()
                .find_map(|declaration| {
                    if let Declaration::Constant {
                        name: constant_name,
                        function_pointer,
                    } = declaration
                    {
                        if constant_name == name {
                            return Some(function_pointer);
                        }
                    }
                    None
                })
                .unwrap()
        }

        pub fn push_inductive(&mut self, name: String, llvm_type: PointerType<'ctx>) {
            self.declarations.push(Declaration::Inductive(
                name.clone(),
                Inductive {
                    name,
                    llvm_type,
                    constructors: vec![],
                },
            ))
        }

        pub fn push_constant_value(&mut self, name: String, function_pointer: PointerValue<'ctx>) {
            self.declarations.push(Declaration::Constant {
                name,
                function_pointer,
            })
        }

        pub fn add_constructor_struct_type(
            &mut self,
            inductive_name: &str,
            constructor_name: String,
            constructor_struct_type: StructType<'ctx>,
        ) {
            self.lookup_inductive_mut(inductive_name)
                .constructors
                .push(Constructor {
                    name: constructor_name,
                    struct_type: constructor_struct_type,
                    function: None,
                });
        }

        pub fn add_constructor_function(
            &mut self,
            inductive_name: &str,
            constructor_name: &str,
            constructor_function: ConstructorFunction<'ctx>,
        ) {
            let constructor = self
                .lookup_inductive_mut(inductive_name)
                .constructors
                .iter_mut()
                .find_map(|constructor| {
                    if constructor.name == constructor_name {
                        return Some(constructor);
                    }
                    None
                })
                .unwrap();

            constructor.function = Some(constructor_function)
        }
    }
}

pub mod local {
    use crate::{hir, hir::ir::DeBruijnIndex};
    use inkwell::values::PointerValue;
    use std::collections::HashSet;

    #[derive(Debug, Clone)]
    pub enum DeBruijnValue<'ctx> {
        RegisterValue(PointerValue<'ctx>),
        StackPointer(PointerValue<'ctx>),
        RecursiveFunction {
            free_debruijn_indexes: HashSet<DeBruijnIndex>,
            function_pointer: PointerValue<'ctx>,
        },
    }

    #[derive(Debug, Clone)]
    pub struct Environment<'ctx> {
        debruijn_values: Vec<DeBruijnValue<'ctx>>,
    }

    impl<'ctx> Environment<'ctx> {
        pub fn new() -> Environment<'ctx> {
            Environment {
                debruijn_values: Vec::new(),
            }
        }

        pub fn push_register_value(&mut self, value: PointerValue<'ctx>) {
            self.debruijn_values
                .push(DeBruijnValue::RegisterValue(value))
        }

        pub fn push_recursive_function(
            &mut self,
            free_debruijn_indexes: HashSet<DeBruijnIndex>,
            function_pointer: PointerValue<'ctx>,
        ) {
            self.debruijn_values.push(DeBruijnValue::RecursiveFunction {
                free_debruijn_indexes,
                function_pointer,
            })
        }

        pub fn pop(&mut self) {
            self.debruijn_values.pop().unwrap();
        }

        pub fn lookup(&self, debruijn_index: DeBruijnIndex) -> &DeBruijnValue<'ctx> {
            hir::ir::debruijn_index_lookup(&self.debruijn_values, debruijn_index)
        }

        pub fn lookup_mut(&mut self, debruijn_index: DeBruijnIndex) -> &mut DeBruijnValue<'ctx> {
            hir::ir::debruijn_index_lookup_mut(&mut self.debruijn_values, debruijn_index)
        }

        pub fn update_register_value_with_stack_pointer(
            &mut self,
            debruijn_index: DeBruijnIndex,
            stack_pointer: PointerValue<'ctx>,
        ) {
            *self.lookup_mut(debruijn_index) = DeBruijnValue::StackPointer(stack_pointer);
        }
    }
}
