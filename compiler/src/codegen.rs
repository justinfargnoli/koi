use crate::hir::ir::{Declaration, Inductive, Term, HIR};
use environment::local;
use inkwell::{
    builder::Builder,
    context::Context as InkwellContext,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicTypeEnum, PointerType, StructType},
    values::{BasicMetadataValueEnum, CallableValue, PointerValue},
    AddressSpace,
};

mod environment {
    pub mod local {
        use crate::hir::ir::DeBruijnIndex;
        use inkwell::values::PointerValue;

        pub struct Environment<'ctx> {
            debruijn_values: Vec<PointerValue<'ctx>>,
        }

        impl<'ctx> Environment<'ctx> {
            pub fn new() -> Environment<'ctx> {
                Environment {
                    debruijn_values: Vec::new(),
                }
            }

            pub fn push(&mut self, value: PointerValue<'ctx>) {
                self.debruijn_values.push(value)
            }

            pub fn pop(&mut self) {
                self.debruijn_values.pop().unwrap();
            }

            pub fn lookup(&self, debruijn_index: DeBruijnIndex) -> &PointerValue<'ctx> {
                self.debruijn_values.get(debruijn_index).unwrap()
            }
        }
    }

    pub mod global {
        use inkwell::types::PointerType;

        use crate::hir::ir::{Identifier, Term};

        pub struct Environment<'ctx> {
            declarations: Vec<Declaration<'ctx>>,
            // TODO: `universe_graph: uGraph.t`
        }

        impl<'ctx> Environment<'ctx> {
            pub fn new() -> Environment<'ctx> {
                Environment {
                    declarations: Vec::new(),
                }
            }

            pub fn lookup_inductive_llvm_type(&self, name: &str) -> PointerType<'ctx> {
                self.lookup_inductive(name).llvm_type // Q: does `llvm_type` need to be cloned?
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

            pub fn add_constructors(
                &mut self,
                inductive_name: &str,
                constructors: Vec<Constructor<'ctx>>,
            ) {
                self.lookup_inductive_mut(inductive_name).constructors = constructors;
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
        }

        enum Declaration<'ctx> {
            Constant(String, ConstantBody),
            Inductive(String, Inductive<'ctx>),
        }

        pub struct Inductive<'ctx> {
            pub name: Identifier,
            pub llvm_type: PointerType<'ctx>,
            pub constructors: Vec<Constructor<'ctx>>,
        }

        pub struct Constructor<'ctx> {
            pub name: Identifier,
            pub llvm_type: PointerType<'ctx>,
        }

        impl<'ctx> Constructor<'ctx> {
            pub fn build(name: Identifier, llvm_type: PointerType<'ctx>) -> Constructor<'ctx> {
                Constructor { name, llvm_type }
            }
        }

        struct ConstantBody {
            typ: Term,
            body: Option<Term>,
            // TODO: `universes: universe_context`
        }
    }
}

pub struct Context<'ctx> {
    context: &'ctx InkwellContext,
    builder: Builder<'ctx>,
    module: Module<'ctx>,
    global: environment::global::Environment<'ctx>,
}

impl<'ctx> Context<'ctx> {
    pub fn build(inkwell_context: &InkwellContext) -> Context {
        Context {
            context: inkwell_context,
            builder: inkwell_context.create_builder(),
            module: inkwell_context.create_module("koi"),
            global: environment::global::Environment::new(),
        }
    }

    pub fn codegen_hir(&mut self, hir: &HIR) {
        for declaration in &hir.declarations {
            match declaration {
                Declaration::Constant(term) => self.codegen_term(&term),
                Declaration::Inductive(inductive) => self.codegen_inductive(&inductive),
            }
        }
        self.module.verify().unwrap();
    }

    pub fn codegen_term(&mut self, term: &Term) {
        if let None = self.module.get_first_function() {
            // Declare the main function
            let llvm_main_function = self.module.add_function(
                "main",
                self.context.void_type().fn_type(&[], false),
                None,
            );
            // Add a basic block to the function.
            let llvm_main_function_entry_basic_block = self
                .context
                .append_basic_block(llvm_main_function, "koi_entry");
            self.builder
                .position_at_end(llvm_main_function_entry_basic_block);
        }

        self.codegen_term_helper(term, &mut local::Environment::new());
    }

    fn llvm_pointer_type(&self) -> PointerType<'ctx> {
        self.context.i8_type().ptr_type(AddressSpace::Generic)
    }

    fn codegen_term_helper(
        &mut self,
        term: &Term,
        local: &mut local::Environment<'ctx>,
    ) -> PointerValue<'ctx> {
        match term {
            Term::DeBruijnIndex(debruijn_index) => local.lookup(*debruijn_index).clone(),
            Term::Lambda { body, .. } => {
                // Get the basic block that we were previously inserting instructions into. This is
                // used later to build the lambda struct.
                let llvm_previous_basic_block = self.builder.get_insert_block().unwrap();

                let llvm_lambda_function_type = self.llvm_pointer_type().fn_type(
                    &[
                        BasicMetadataTypeEnum::from(self.llvm_pointer_type()), // parameter
                        BasicMetadataTypeEnum::from(self.llvm_pointer_type()), // captures
                    ],
                    false,
                );
                let llvm_lambda_function_value =
                    self.module
                        .add_function("", llvm_lambda_function_type, None);

                // Add a basic block to the function.
                let llvm_function_entry_basic_block = self
                    .context
                    .append_basic_block(llvm_lambda_function_value, "koi_entry");
                self.builder
                    .position_at_end(llvm_function_entry_basic_block);

                // Push the parameter to the local environment.
                // TODO: Push the captured variables.
                local.push(
                    llvm_lambda_function_value
                        .get_first_param()
                        .unwrap()
                        .into_pointer_value(),
                );

                // Codegen the body.
                let return_value = self.codegen_term_helper(body, local);

                // Reset the local environment.
                local.pop();

                // Return the result of the body.
                self.builder.build_return(Some(&return_value));

                llvm_lambda_function_value.verify(true);

                // Set the builders back to the position it was at before codegening this lambda.
                self.builder.position_at_end(llvm_previous_basic_block);

                let llvm_lambda_function_ptr = llvm_lambda_function_value
                    .as_global_value()
                    .as_pointer_value();

                // TODO: Build the `captures` struct.
                // TODO: Get the indexes of all free variables in the lambda and put them in `llvm_captures_struct`
                let llvm_captures_struct = self.context.const_struct(&[], false);
                let llvm_captures_struct_ptr = self
                    .builder
                    .build_malloc(llvm_captures_struct.get_type(), "captures_struct_pointer")
                    .unwrap();
                self.builder
                    .build_store(llvm_captures_struct_ptr, llvm_captures_struct);

                // Build the struct that represents this lambda.
                // struct Lambda {
                //   function* lambda,
                //   struct* captures,
                // }
                let llvm_lambda_struct = self.context.const_struct(
                    &[
                        // llvm_lambda_function_ptr.into(),
                        // llvm_captures_struct_ptr.into(),
                    ],
                    false,
                );
                let llvm_lambda_struct_ptr = self
                    .builder
                    .build_malloc(llvm_lambda_struct.get_type(), "lambda_struct_pointer")
                    .unwrap();
                self.builder
                    .build_store(llvm_lambda_struct_ptr, llvm_lambda_struct);

                // Return a pointer to the struct that represents this lambda.
                llvm_lambda_struct_ptr
            }
            Term::Application { function, argument } => {
                let llvm_function_struct_pointer = self.codegen_term_helper(function, local);
                // Get the pointer to the function.
                let llvm_function_pointer = self
                    .builder
                    .build_struct_gep(llvm_function_struct_pointer, 0, "function_pointer")
                    .unwrap();
                // Get the pointer to the captures struct.
                let llvm_captures_struct_pointer = self
                    .builder
                    .build_struct_gep(llvm_function_struct_pointer, 1, "captures_struct_pointer")
                    .unwrap();

                // Get the argument to the function.
                let llvm_argument_pointer = self.codegen_term_helper(argument, local);

                // Call the function and return the pointer that the function returns.
                self.builder
                    .build_call(
                        CallableValue::try_from(llvm_function_pointer).unwrap(),
                        &[
                            BasicMetadataValueEnum::from(llvm_argument_pointer),
                            BasicMetadataValueEnum::from(llvm_captures_struct_pointer),
                        ],
                        "call",
                    )
                    .try_as_basic_value()
                    .unwrap_left()
                    .into_pointer_value()
            }
            _ => todo!("{:#?}", term),
        }
    }

    // let inductive = self.global.lookup_inductive(inductive_name);
    // let constructor = inductive.constructors.get(*index).unwrap();
    // let llvm_constructor_value = self
    //     .builder
    //     .build_malloc(
    //         constructor.llvm_type.get_element_type().into_struct_type(),
    //         &constructor.name,
    //     )
    //     .unwrap();

    // let llvm_first_constructor_field = self
    //     .builder
    //     .build_struct_gep(llvm_constructor_value, 0, "")
    //     .unwrap();
    // self.builder
    //     .build_store(llvm_first_constructor_field, llvm_argument_pointer);

    // llvm_constructor_value

    pub fn constructor_llvm_name(inductive_name: &str, constructor_name: &str) -> String {
        format!("{}_{}", inductive_name, constructor_name)
    }

    fn codegen_constructor_type(&self, constructor_type: &Term) -> Vec<BasicTypeEnum> {
        match constructor_type {
            Term::DependentProduct {
                parameter_name: _,
                parameter_type,
                return_type,
            } => {
                let mut field_types = self.codegen_constructor_type(&parameter_type);
                field_types.append(&mut self.codegen_constructor_type(&return_type));
                field_types
            }
            Term::Inductive(name, _) => {
                vec![self.global.lookup_inductive_llvm_type(&name).into()]
            }
            _ => panic!(),
        }
    }

    pub fn codegen_inductive(&mut self, inductive: &Inductive) {
        // Initialize the llvm struct that will have the largest width of any enum variant.
        let inductive_llvm_struct_type = self.context.opaque_struct_type(&inductive.name);

        // Add the llvm struct to the global environment
        self.global.push_inductive(
            inductive.name.clone(),
            inductive_llvm_struct_type.ptr_type(AddressSpace::Generic),
        );

        // Codegen the struct type for each constructor
        let constructor_llvm_types: Vec<StructType> = inductive
            .constructors
            .iter()
            .map(|constructor| {
                let constructor_llvm_type =
                    self.context
                        .opaque_struct_type(&Context::constructor_llvm_name(
                            &inductive.name,
                            &constructor.name,
                        ));

                let field_types = self.codegen_constructor_type(&constructor.typ);
                constructor_llvm_type.set_body(&field_types, false);

                constructor_llvm_type
            })
            .collect();

        // TODO: Codegen llvm function for each constructor.

        // Set the body of `inductive_llvm_struct_type` to be that of the largest constructor
        let largest_constructor_llvm_type = constructor_llvm_types
            .iter()
            .map(|constructor_llvm_type| {
                let field_count = constructor_llvm_type.get_field_types().len();
                (field_count, constructor_llvm_type)
            })
            .max_by(|(field_count_1, _), (field_count_2, _)| {
                usize::cmp(field_count_1, field_count_2)
            })
            .and_then(|(_, constructor)| Some(constructor));
        if let Some(constructor_type) = largest_constructor_llvm_type {
            inductive_llvm_struct_type.set_body(&constructor_type.get_field_types(), false);
        }

        // Add the constructors to the global environment
        let inductive_llvm_constructors = constructor_llvm_types
            .into_iter()
            .enumerate()
            .map(|(i, constructor_llvm_type)| {
                environment::global::Constructor::build(
                    inductive.constructors.get(i).unwrap().name.clone(),
                    constructor_llvm_type.ptr_type(AddressSpace::Generic),
                )
            })
            .collect();
        self.global
            .add_constructors(&inductive.name, inductive_llvm_constructors);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::examples;

    #[test]
    fn nat_type() {
        let inductive_nat = &examples::nat();

        let inkwell_context = InkwellContext::create();
        let mut context = Context::build(&inkwell_context);
        context.codegen_inductive(inductive_nat);

        let nat_llvm_struct = context.module.get_struct_type(&inductive_nat.name).unwrap();
        let nat_field_types = nat_llvm_struct.get_field_types();
        assert_eq!(nat_field_types.len(), 2);

        let nat_llvm_ptr = context
            .global
            .lookup_inductive_llvm_type(&inductive_nat.name)
            .into();

        let nat_zero_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(
                &inductive_nat.name,
                &inductive_nat.constructors.get(0).unwrap().name,
            ))
            .unwrap();
        let zero_field_types = nat_zero_llvm_struct.get_field_types();
        assert_eq!(zero_field_types.len(), 1);
        assert_eq!(zero_field_types[0], nat_llvm_ptr);

        let nat_successor_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(
                &inductive_nat.name,
                &inductive_nat.constructors.get(1).unwrap().name,
            ))
            .unwrap();
        let successor_field_types = nat_successor_llvm_struct.get_field_types();
        assert_eq!(successor_field_types.len(), 2);
        assert_eq!(successor_field_types, nat_field_types);
        assert_eq!(successor_field_types[0], nat_llvm_ptr);
        assert_eq!(successor_field_types[1], nat_llvm_ptr);
    }

    #[test]
    fn nat_identity() {
        let identity_function = examples::nat_identity();

        let inkwell_context = InkwellContext::create();
        let mut context = Context::build(&inkwell_context);
        context.codegen_term(&identity_function);

        let llvm_identity_function = context.module.get_last_function().unwrap();

        assert_eq!(llvm_identity_function.get_params().len(), 2);
        llvm_identity_function
            .get_params()
            .iter()
            .for_each(|parameter| {
                let parameter_pointer = parameter.into_pointer_value();
                assert_eq!(
                    parameter_pointer
                        .get_type()
                        .get_element_type()
                        .into_int_type(),
                    context.context.i8_type()
                );
            });

        let llvm_basic_blocks = llvm_identity_function.get_basic_blocks();
        assert_eq!(llvm_basic_blocks.len(), 1);

        let llvm_first_basic_block = llvm_basic_blocks.get(0).unwrap();
        assert_eq!(
            llvm_first_basic_block.get_first_instruction(),
            llvm_first_basic_block.get_last_instruction()
        );
    }

    #[test]
    #[should_panic] // TODO remove this`
    fn nat_one() {
        let nat_one = examples::nat_one();

        let inkwell_context = InkwellContext::create();
        let mut context = Context::build(&inkwell_context);
        context.codegen_term(&nat_one);
    }
}
