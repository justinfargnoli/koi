use crate::hir::ir::{Declaration, Inductive, Term, HIR};
use environment::local;
use inkwell::{
    builder::Builder,
    context::Context as InkwellContext,
    module::Module,
    types::{BasicType, BasicTypeEnum, PointerType, StructType},
    values::{CallableValue, FunctionValue, InstructionOpcode, PointerValue},
    AddressSpace,
};

use self::environment::global::Constructor;

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
        use inkwell::{
            types::{PointerType, StructType},
            values::PointerValue,
        };

        use crate::hir::ir::{Identifier, Term};

        #[derive(Debug)]
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
                self.lookup_inductive(name).llvm_type
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

            pub fn add_constructor(
                &mut self,
                inductive_name: &str,
                constructors: Constructor<'ctx>,
            ) {
                self.lookup_inductive_mut(inductive_name)
                    .constructors
                    .push(constructors);
            }
        }

        #[derive(Debug)]
        enum Declaration<'ctx> {
            Constant(String, ConstantBody),
            Inductive(String, Inductive<'ctx>),
        }

        #[derive(Debug)]
        pub struct Inductive<'ctx> {
            pub name: Identifier,
            pub llvm_type: PointerType<'ctx>,
            pub constructors: Vec<Constructor<'ctx>>,
        }

        #[derive(Debug)]
        pub struct Constructor<'ctx> {
            pub name: Identifier,
            pub llvm_struct_type: StructType<'ctx>,
            pub llvm_function: PointerValue<'ctx>,
        }

        #[derive(Debug)]
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
                Declaration::Constant(term) => self.codegen_term(term),
                Declaration::Inductive(inductive) => self.codegen_inductive(inductive),
            }
        }
        self.module.verify().unwrap();
    }

    pub fn codegen_term(&self, term: &Term) {
        if self.module.get_first_function().is_none() {
            // Declare the main function
            let llvm_main_function = self.module.add_function(
                "main",
                self.context.void_type().fn_type(&[], false),
                None,
            );
            // Add a basic block to the function.
            let llvm_main_function_entry_basic_block = self
                .context
                .append_basic_block(llvm_main_function, "main_entry");
            self.builder
                .position_at_end(llvm_main_function_entry_basic_block);
        }

        self.codegen_term_helper(term, &mut local::Environment::new());
    }

    fn llvm_pointer_type(&self) -> PointerType<'ctx> {
        self.context.i8_type().ptr_type(AddressSpace::Generic)
    }

    fn codegen_term_helper(
        &self,
        term: &Term,
        local: &mut local::Environment<'ctx>,
    ) -> PointerValue<'ctx> {
        match term {
            Term::DeBruijnIndex(debruijn_index) => *local.lookup(*debruijn_index),
            Term::Lambda { body, .. } => {
                // Get the basic block that we were previously inserting instructions into. This is
                // used later to build the lambda struct.
                let llvm_previous_basic_block = self.builder.get_insert_block().unwrap();

                let llvm_function =
                    self.initialize_curried_llvm_function(&self.llvm_pointer_type(), "lambda");

                // Push the parameter to the local environment.
                // TODO: Push the captured variables.
                local.push(
                    llvm_function
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

                llvm_function.verify(true);

                // Set the builders back to the position it was at before codegening this lambda.
                self.builder.position_at_end(llvm_previous_basic_block);

                let llvm_lambda_function_ptr = llvm_function.as_global_value().as_pointer_value();

                // TODO: Build the `captures` struct. Get the indexes of all free variables in the lambda
                // and put them in `llvm_captures_struct`.
                let llvm_captures_struct_type = self.context.struct_type(&[], false);
                let llvm_captures_struct_ptr = self
                    .builder
                    .build_malloc(llvm_captures_struct_type, "captures_struct_pointer")
                    .unwrap();
                // Store into struct fields

                // Build the struct that represents this lambda.
                // struct Lambda {
                //   function* lambda,
                //   struct* captures,
                // }
                let llvm_lambda_struct_ptr = self
                    .builder
                    .build_malloc(
                        self.context.struct_type(
                            &[
                                llvm_lambda_function_ptr.get_type().into(),
                                llvm_captures_struct_ptr.get_type().into(),
                            ],
                            false,
                        ),
                        "lambda_struct_pointer",
                    )
                    .unwrap();
                // Store `lambda`
                let llvm_lambda_function_field_ptr = self
                    .builder
                    .build_struct_gep(llvm_lambda_struct_ptr, 0, "lambda_function_pointer")
                    .unwrap();
                self.builder
                    .build_store(llvm_lambda_function_field_ptr, llvm_lambda_function_ptr);
                // Store `captures`
                let llvm_captures_field_ptr = self
                    .builder
                    .build_struct_gep(llvm_lambda_struct_ptr, 1, "lambda_function_pointer")
                    .unwrap();
                self.builder
                    .build_store(llvm_captures_field_ptr, llvm_captures_struct_ptr);

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
                            llvm_argument_pointer.into(),
                            llvm_captures_struct_pointer.into(),
                        ],
                        "call",
                    )
                    .try_as_basic_value()
                    .unwrap_left()
                    .into_pointer_value()
            }
            Term::Constructor(_inductive_name, _branch_index, _) => {
                todo!()
            }
            Term::Sort(_) | Term::DependentProduct { .. } => unreachable!(),
            _ => todo!("{:#?}", term),
        }
    }

    fn initialize_curried_llvm_function(
        &self,
        return_type: &dyn BasicType<'ctx>,
        name: &str,
    ) -> FunctionValue<'ctx> {
        // Create the function for this constructor.
        let llvm_function_type = return_type.ptr_type(AddressSpace::Generic).fn_type(
            &[
                self.llvm_pointer_type().into(),
                self.llvm_pointer_type().into(),
            ],
            false,
        );
        let llvm_function_value = self.module.add_function(name, llvm_function_type, None);
        // Add a basic block to the function.
        let llvm_function_entry_basic_block = self
            .context
            .append_basic_block(llvm_function_value, "entry");
        self.builder
            .position_at_end(llvm_function_entry_basic_block);

        llvm_function_value
    }

    // Codegen llvm function for each constructor.
    // TODO: Enable curried constructors.
    fn codegen_constructor_function(
        &self,
        constructor_index: u8,
        constructor_llvm_name: &str,
        constructor_llvm_struct_type: StructType<'ctx>,
    ) -> PointerValue<'ctx> {
        let llvm_function = self
            .initialize_curried_llvm_function(&constructor_llvm_struct_type, constructor_llvm_name);

        // Allocate memory for the constructor's struct on the heap.
        let llvm_constructor_struct_pointer = self
            .builder
            .build_malloc(constructor_llvm_struct_type, "constructor_struct")
            .unwrap();

        // Write the tag.
        let llvm_constructor_tag_pointer = self
            .builder
            .build_struct_gep(llvm_constructor_struct_pointer, 0, "constructor_tag")
            .unwrap();
        self.builder.build_store(
            llvm_constructor_tag_pointer,
            self.context
                .i8_type()
                .const_int(constructor_index as u64, false),
        );

        // Write to the fields of the constructor.
        for i in 1..constructor_llvm_struct_type.get_field_types().len() {
            // Computer the address of the field that we will write to.
            let llvm_constructor_field = self
                .builder
                .build_struct_gep(
                    llvm_constructor_struct_pointer,
                    i as u32,
                    &format!("field_{}", i),
                )
                .unwrap();

            if i == (constructor_llvm_struct_type.get_field_types().len() - 1) {
                // Cast the type of the pointer to the type of the field.
                let llvm_capture_field_pointer = self.builder.build_cast(
                    InstructionOpcode::BitCast,
                    llvm_function
                        .get_first_param()
                        .unwrap()
                        .into_pointer_value(),
                    BasicTypeEnum::try_from(llvm_constructor_field.get_type().get_element_type())
                        .unwrap(),
                    "pointer_cast",
                );

                self.builder
                    .build_store(llvm_constructor_field, llvm_capture_field_pointer);
            } else {
                // Get the pointer value for field `i` from the capture struct.
                let llvm_capture_field_i = self
                    .builder
                    .build_struct_gep(
                        llvm_function.get_last_param().unwrap().into_pointer_value(),
                        (i - 1) as u32, // Subtract one to account for the tag that we've added to the struct.
                        &format!("environment_field_{}", i),
                    )
                    .unwrap();

                // Cast the type of the pointer to the type of the field.
                let llvm_capture_field_pointer = self.builder.build_cast(
                    InstructionOpcode::BitCast,
                    llvm_capture_field_i,
                    BasicTypeEnum::try_from(llvm_constructor_field.get_type().get_element_type())
                        .unwrap(),
                    "pointer_cast",
                );

                self.builder
                    .build_store(llvm_constructor_field, llvm_capture_field_pointer);
            }
        }

        // Return the struct that holds the data for this constructor.
        self.builder
            .build_return(Some(&llvm_constructor_struct_pointer));

        // Return a pointer to this constructor.
        llvm_function.as_global_value().as_pointer_value()
    }

    pub fn constructor_llvm_name(inductive_name: &str, constructor_name: &str) -> String {
        format!("{}_{}", inductive_name, constructor_name)
    }

    fn codegen_constructor_type_helper(
        &self,
        constructor_type: &Term,
        accumulator: &mut Vec<BasicTypeEnum<'ctx>>,
    ) {
        match constructor_type {
            Term::DependentProduct {
                parameter_type,
                return_type,
                ..
            } => {
                self.codegen_constructor_type_helper(parameter_type, accumulator);
                self.codegen_constructor_type_helper(return_type, accumulator);
            }
            Term::Inductive(name, _) => {
                accumulator.push(self.global.lookup_inductive_llvm_type(name).into());
            }
            _ => panic!(),
        }
    }

    fn codegen_constructor_type(
        &self,
        constructor_llvm_name: &str,
        constructor_type: &Term,
    ) -> StructType<'ctx> {
        let constructor_llvm_type = self.context.opaque_struct_type(constructor_llvm_name);

        let mut field_types = vec![self.context.i8_type().into()];
        self.codegen_constructor_type_helper(constructor_type, &mut field_types);
        field_types.pop();

        constructor_llvm_type.set_body(&field_types, false);

        constructor_llvm_type
    }

    fn codegen_constructor(
        &mut self,
        inductive_name: &str,
        constructor_index: u8,
        constructor: &crate::hir::ir::Constructor,
    ) {
        let constructor_llvm_name =
            Context::constructor_llvm_name(inductive_name, &constructor.name);

        let constructor_llvm_type =
            self.codegen_constructor_type(&constructor_llvm_name, &constructor.typ);

        self.global.add_constructor(
            inductive_name,
            Constructor {
                name: constructor.name.clone(),
                llvm_struct_type: constructor_llvm_type,
                llvm_function: self.codegen_constructor_function(
                    constructor_index,
                    &constructor_llvm_name,
                    constructor_llvm_type,
                ),
            },
        );
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
        inductive
            .constructors
            .iter()
            .enumerate()
            .for_each(|(index, constructor)| {
                self.codegen_constructor(&inductive.name, index as u8, constructor)
            });

        // Set the body of `inductive_llvm_struct_type` to be that of the largest constructor
        let largest_constructor_llvm_type = self
            .global
            .lookup_inductive(&inductive.name)
            .constructors
            .iter()
            .map(|constructor| {
                let constructor_llvm_type = constructor.llvm_struct_type;
                let field_count = constructor_llvm_type.get_field_types().len();
                (field_count, constructor_llvm_type)
            })
            .max_by(|(field_count_1, _), (field_count_2, _)| {
                usize::cmp(field_count_1, field_count_2)
            })
            .map(|(_, constructor)| constructor);
        if let Some(constructor_type) = largest_constructor_llvm_type {
            inductive_llvm_struct_type.set_body(&constructor_type.get_field_types(), false);
        }
    }
}

#[cfg(test)]
mod tests {
    use inkwell::types::BasicType;

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

        let nat_zero_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(
                &inductive_nat.name,
                &inductive_nat.constructors.get(0).unwrap().name,
            ))
            .unwrap();
        let zero_field_types = nat_zero_llvm_struct.get_field_types();
        assert_eq!(zero_field_types.len(), 1);
        assert_eq!(
            zero_field_types[0],
            context.context.i8_type().as_basic_type_enum()
        );

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
        assert_eq!(
            successor_field_types[0],
            context.context.i8_type().as_basic_type_enum()
        );
        assert_eq!(
            successor_field_types[1],
            nat_llvm_struct
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()
        );

        println!("{}", context.module.print_to_string().to_string());
    }

    #[test]
    fn nat_identity() {
        let identity_function = examples::nat_identity();

        let inkwell_context = InkwellContext::create();
        let context = Context::build(&inkwell_context);
        context.codegen_term(&identity_function);

        println!("{}", context.module.print_to_string().to_string());
    }

    #[test]
    fn nat_one() {
        let nat_one = examples::nat_one();

        let inkwell_context = InkwellContext::create();
        let context = Context::build(&inkwell_context);
        context.codegen_term(&nat_one);
    }
}
