mod environment;
mod passes;

use crate::hir::ir::{DeBruijnIndex, Declaration, Inductive, Name, Term, Undefined, HIR};
use environment::{global, global::ConstructorFunction, local, local::DeBruijnValue};
use inkwell::{
    builder::Builder,
    context::Context as InkwellContext,
    module::{Linkage, Module},
    types::{BasicType, BasicTypeEnum, PointerType, StructType},
    values::{CallableValue, FunctionValue, PointerValue},
    AddressSpace,
};
use passes::free_variables::free_variables;
use std::{collections::HashSet, fs, iter, process::Command, thread};

enum CodegenFunctionConfiguration {
    Lambda,
    Fixpoint,
    OuterConstructorFunction,
}

pub struct Context<'ctx> {
    context: &'ctx InkwellContext,
    builder: Builder<'ctx>,
    module: Module<'ctx>,
    global: global::Environment<'ctx>,
}

impl<'ctx> Context<'ctx> {
    pub fn build(inkwell_context: &InkwellContext) -> Context {
        Context {
            context: inkwell_context,
            builder: inkwell_context.create_builder(),
            module: inkwell_context.create_module("koi"),
            global: global::Environment::new(),
        }
    }

    pub fn run_module(&self) {
        let test_directory_name = "tests/codegen";
        fs::create_dir_all(test_directory_name).unwrap();

        let file_name = format!(
            "{}/test_{}",
            test_directory_name,
            thread::current().id().as_u64()
        );

        let llvm_ir_file_name = format!("{}.ll", file_name);
        let llvm_ir = self.module.print_to_string().to_string();

        fs::write(&llvm_ir_file_name, llvm_ir).unwrap();

        let clang_output = Command::new("clang")
            .args([
                llvm_ir_file_name,
                format!("-o{}", file_name),
                "-Wno-override-module".to_string(),
            ])
            .output()
            .unwrap();
        assert!(clang_output.status.success());
        assert!(clang_output.stdout.is_empty());
        assert!(clang_output.stderr.is_empty());

        let binary_output = Command::new(format!("./{}", file_name)).output().unwrap();
        assert!(binary_output.status.success());
        assert!(binary_output.stdout.is_empty());
        assert!(binary_output.stderr.is_empty());
    }

    fn codegen_main(&self) {
        let main_str = "main";
        assert!(self.module.get_function(main_str).is_none());
        // Declare the main function
        let llvm_main_function =
            self.module
                .add_function(main_str, self.context.i32_type().fn_type(&[], false), None);

        // Add a basic block to the function.
        let llvm_main_function_entry_basic_block =
            self.context.append_basic_block(llvm_main_function, "entry");
        self.builder
            .position_at_end(llvm_main_function_entry_basic_block);
    }

    pub fn codegen_hir(&mut self, hir: &HIR) {
        // Codegen main if it hasn't already been generated.
        self.codegen_main();

        for declaration in &hir.declarations {
            self.builder.position_at_end(
                self.module
                    .get_function("main")
                    .unwrap()
                    .get_last_basic_block()
                    .unwrap(),
            );

            match declaration {
                Declaration::Constant(term) => {
                    self.codegen_term_helper(term, &mut local::Environment::new());

                    // Add value to global environment if it has a name.
                    let global_constant_name = match term {
                        Term::Lambda {
                            name: Name::Named(name),
                            ..
                        } => Some(name),
                        Term::Fixpoint { body, .. } => match &**body {
                            Term::Lambda {
                                name: Name::Named(name),
                                ..
                            } => Some(name),
                            _ => None,
                        },
                        _ => None,
                    };

                    match global_constant_name {
                        Some(name) => self.global.push_constant_value(
                            name.clone(),
                            self.module
                                .get_function(name)
                                .unwrap()
                                .as_global_value()
                                .as_pointer_value(),
                        ),
                        None => (),
                    }
                }
                Declaration::Inductive(inductive) => self.codegen_inductive(inductive),
            }
        }

        self.builder.position_at_end(
            self.module
                .get_function("main")
                .unwrap()
                .get_last_basic_block()
                .unwrap(),
        );
        self.builder
            .build_return(Some(&self.context.i32_type().const_int(0, false)));

        println!("{}", self.module.print_to_string().to_string());
        self.module.verify().unwrap();
    }

    pub fn codegen_term(&self, term: &Term) -> PointerValue<'ctx> {
        // Codegen main if it hasn't already been generated.
        self.codegen_main();

        self.codegen_term_helper(term, &mut local::Environment::new())
    }

    fn codegen_term_helper(
        &self,
        term: &Term,
        local: &mut local::Environment<'ctx>,
    ) -> PointerValue<'ctx> {
        match term {
            Term::DeBruijnIndex(debruijn_index) => {
                self.codegen_debruijn_index(*debruijn_index, local)
            }
            Term::Lambda { .. } => {
                self.codegen_function(term, local, &CodegenFunctionConfiguration::Lambda)
            }
            Term::Application { function, argument } => {
                let llvm_function_struct_pointer = self.codegen_term_helper(function, local);

                let llvm_function_struct_pointer_casted = self
                    .builder
                    .build_bitcast(
                        llvm_function_struct_pointer,
                        self.function_struct_pointer_type(),
                        "llvm_function_struct_pointer_casted",
                    )
                    .into_pointer_value();

                // Get the function pointer.
                let llvm_function_pointer_pointer = self
                    .builder
                    .build_struct_gep(
                        llvm_function_struct_pointer_casted,
                        0,
                        "application_lambda_struct_function_address",
                    )
                    .unwrap();
                let llvm_function_pointer = self
                    .builder
                    .build_load(
                        llvm_function_pointer_pointer,
                        "application_function_pointer",
                    )
                    .into_pointer_value();
                // Get the pointer to the captures struct.
                let llvm_captures_struct_pointer_pointer = self
                    .builder
                    .build_struct_gep(
                        llvm_function_struct_pointer_casted,
                        1,
                        "application_lambda_struct_captures_address",
                    )
                    .unwrap();
                let llvm_captures_struct_pointer = self
                    .builder
                    .build_load(
                        llvm_captures_struct_pointer_pointer,
                        "application_lambda_struct_captures_pointer",
                    )
                    .into_pointer_value();

                // Get the argument to the function.
                let llvm_argument_pointer = self.codegen_term_helper(argument, local);

                // Cast the argument to be an `i8*`.
                let llvm_argument_pointer_cast = self
                    .builder
                    .build_bitcast(
                        llvm_argument_pointer,
                        self.pointer_type(),
                        "application_argument_cast",
                    )
                    .into_pointer_value();

                // Call the function and return the pointer that the function returns.
                self.builder
                    .build_call(
                        CallableValue::try_from(llvm_function_pointer).unwrap(),
                        &[
                            llvm_argument_pointer_cast.into(),
                            llvm_captures_struct_pointer.into(),
                        ],
                        "call",
                    )
                    .try_as_basic_value()
                    .unwrap_left()
                    .into_pointer_value()
            }
            Term::Constant(name) => {
                let constant_function_pointer = self.global.lookup_constant_value(name);
                let empty_captures_struct = self.codegen_pointer_to_empty_struct();
                self.codegen_lambda_struct(constant_function_pointer, empty_captures_struct)
            }
            Term::Constructor(inductive_name, branch_index) => {
                let llvm_constructor_value = self
                    .global
                    .lookup_constructor_function(inductive_name, *branch_index);

                match llvm_constructor_value {
                    ConstructorFunction::ZeroArgumentFunctionPointer(function_pointer) => self
                        .builder
                        .build_call(
                            CallableValue::try_from(function_pointer).unwrap(),
                            &[self.null_pointer().into(), self.null_pointer().into()],
                            "call_zero_argument_constructor",
                        )
                        .try_as_basic_value()
                        .unwrap_left()
                        .into_pointer_value(),
                    ConstructorFunction::FunctionPointer(function_pointer) => {
                        let temp_llvm_constructor_empty_captures_struct =
                            self.codegen_pointer_to_empty_struct();

                        self.codegen_lambda_struct(
                            function_pointer,
                            temp_llvm_constructor_empty_captures_struct,
                        )
                    }
                }
            }
            Term::Match {
                inductive_name,
                scrutinee,
                branches,
                ..
            } => {
                let scrutinee_llvm_value = self.codegen_term_helper(scrutinee, local);

                let inductive = self.global.lookup_inductive(inductive_name);

                let casted_scrutinee_llvm_value = self
                    .builder
                    .build_bitcast(
                        scrutinee_llvm_value,
                        inductive.llvm_type,
                        "cast_scrutinee_to_inductive_llvm_type",
                    )
                    .into_pointer_value();

                let scrutinee_tag_llvm_address = self
                    .builder
                    .build_struct_gep(casted_scrutinee_llvm_value, 0, "address_of_inductive_tag")
                    .unwrap();
                let scrutinee_tag_llvm_value = self
                    .builder
                    .build_load(scrutinee_tag_llvm_address, "inductive_tag")
                    .into_int_value();

                let llvm_match_expression_value = self
                    .builder
                    .build_alloca(self.pointer_type(), "match_expression_value");

                let current_basic_block = self.builder.get_insert_block().unwrap();

                let llvm_switch_post_dominator_basic_block = self.context.append_basic_block(
                    self.builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap(),
                    "switch_post_dominator",
                );

                assert_eq!(inductive.constructors.len(), branches.len());
                let llvm_switch_cases = inductive
                    .constructors
                    .iter()
                    .zip(branches.iter())
                    .enumerate()
                    .map(|(i, (constructor, branch))| {
                        let llvm_switch_case_basic_block = self.context.append_basic_block(
                            self.builder
                                .get_insert_block()
                                .unwrap()
                                .get_parent()
                                .unwrap(),
                            format!("switch_{}_case", i).as_str(),
                        );
                        self.builder.position_at_end(llvm_switch_case_basic_block);

                        let llvm_scrutinee_casted_to_constructor_ptr = self
                            .builder
                            .build_bitcast(
                                scrutinee_llvm_value,
                                constructor.struct_type.ptr_type(AddressSpace::Generic),
                                "cast_to_inductive_variant_type",
                            )
                            .into_pointer_value();

                        for i in 1..constructor.struct_type.get_field_types().len() {
                            let constructor_field_i_address = self
                                .builder
                                .build_struct_gep(
                                    llvm_scrutinee_casted_to_constructor_ptr,
                                    i.try_into().unwrap(),
                                    &format!("constructor_field_{}_address", i),
                                )
                                .unwrap();
                            let constructor_field_i = self
                                .builder
                                .build_load(
                                    constructor_field_i_address,
                                    &format!("constructor_field_{}", i),
                                )
                                .into_pointer_value();

                            local.push_register_value(constructor_field_i);
                        }

                        let llvm_case_expression_value = self.codegen_term_helper(branch, local);

                        for _ in 1..constructor.struct_type.get_field_types().len() {
                            local.pop();
                        }

                        let casted_llvm_case_expression_value = self.builder.build_bitcast(
                            llvm_case_expression_value,
                            self.pointer_type(),
                            "case_expression_value_cast",
                        );
                        self.builder.build_store(
                            llvm_match_expression_value,
                            casted_llvm_case_expression_value,
                        );

                        self.builder
                            .build_unconditional_branch(llvm_switch_post_dominator_basic_block);

                        (
                            self.context
                                .i8_type()
                                .const_int(i.try_into().unwrap(), false),
                            llvm_switch_case_basic_block,
                        )
                    })
                    .collect::<Vec<_>>();

                let llvm_switch_default_basic_block = self.context.append_basic_block(
                    self.builder
                        .get_insert_block()
                        .unwrap()
                        .get_parent()
                        .unwrap(),
                    "switch_default_case",
                );
                self.builder
                    .position_at_end(llvm_switch_default_basic_block);
                self.codegen_exit_with_failure();

                self.builder.position_at_end(current_basic_block);

                self.builder.build_switch(
                    scrutinee_tag_llvm_value,
                    llvm_switch_default_basic_block,
                    llvm_switch_cases.as_slice(),
                );

                self.builder
                    .position_at_end(llvm_switch_post_dominator_basic_block);

                llvm_match_expression_value
            }
            Term::Fixpoint { .. } => {
                self.codegen_function(term, local, &CodegenFunctionConfiguration::Fixpoint)
            }
            Term::Undefined(undefined) => match undefined {
                Undefined::CodegenInnerConstructorFunction {
                    constructor_index,
                    inductive_name,
                    ..
                } => {
                    let constructor_struct_type = self.global.lookup_constructor_struct_type(
                        inductive_name,
                        (*constructor_index).try_into().unwrap(),
                    );

                    // Allocate memory for the constructor's struct on the heap.
                    let llvm_constructor_struct_pointer = self
                        .builder
                        .build_malloc(constructor_struct_type, "constructor_struct")
                        .unwrap();

                    // Write the tag.
                    let llvm_constructor_tag_address = self
                        .builder
                        .build_struct_gep(llvm_constructor_struct_pointer, 0, "constructor_tag")
                        .unwrap();
                    self.builder.build_store(
                        llvm_constructor_tag_address,
                        self.context
                            .i8_type()
                            .const_int(*constructor_index as u64, false),
                    );

                    // Write to the fields of the constructor.
                    assert_ne!(constructor_struct_type.get_field_types().len(), 0);
                    let constructor_parameter_count =
                        Context::constructor_parameter_count(&constructor_struct_type);
                    for (constructor_struct_index, debruijn_index) in iter::zip(
                        1..=constructor_parameter_count,
                        (0..constructor_parameter_count).rev(),
                    ) {
                        // Compute the address of the field that we will write to.
                        let llvm_constructor_field_address = self
                            .builder
                            .build_struct_gep(
                                llvm_constructor_struct_pointer,
                                constructor_struct_index as u32,
                                &format!("field_{}_address", constructor_struct_index),
                            )
                            .unwrap();

                        let debruijn_value = self.codegen_debruijn_index(debruijn_index, local);
                        let debruijn_value_casted = self.builder.build_bitcast(
                            debruijn_value,
                            BasicTypeEnum::try_from(
                                llvm_constructor_field_address.get_type().get_element_type(),
                            )
                            .unwrap(),
                            &format!("field_{}_debruijn_value_cast", constructor_struct_index),
                        );

                        self.builder
                            .build_store(llvm_constructor_field_address, debruijn_value_casted);
                    }

                    llvm_constructor_struct_pointer
                }
                Undefined::Empty => panic!(),
            },
            Term::Sort(_) | Term::DependentProduct { .. } | Term::Inductive(_) => unreachable!(),
        }
    }

    fn initialize_function(
        &self,
        return_type: &dyn BasicType<'ctx>,
        name: &str,
    ) -> FunctionValue<'ctx> {
        // Create the function for this constructor.
        let llvm_function_type = return_type.fn_type(
            &[self.pointer_type().into(), self.pointer_type().into()],
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

    fn codegen_capturing(
        &self,
        free_debruijn_indexes: &HashSet<DeBruijnIndex>,
        local: &local::Environment<'ctx>,
    ) -> PointerValue<'ctx> {
        // Build the `captures` struct.
        let llvm_captures_struct_type = self.context.struct_type(
            vec![self.pointer_type().into(); free_debruijn_indexes.len()].as_slice(),
            false,
        );
        let llvm_captures_struct_ptr = self
            .builder
            .build_malloc(llvm_captures_struct_type, "captures_struct_pointer")
            .unwrap();

        // Put free variables in `llvm_captures_struct`.
        for (i, free_debruijn_index) in free_debruijn_indexes.iter().enumerate() {
            let llvm_captures_struct_field_address = self
                .builder
                .build_struct_gep(
                    llvm_captures_struct_ptr,
                    i.try_into().unwrap(),
                    &format!("captures_struct_field_{}_address", i),
                )
                .unwrap();

            let debruijn_value = self.codegen_debruijn_index(*free_debruijn_index, local);

            self.builder
                .build_store(llvm_captures_struct_field_address, debruijn_value);
        }

        llvm_captures_struct_ptr
    }

    fn name_parameter_type_body_from_lambda(lambda: &Term) -> (&Name, &Term, &Term) {
        match lambda {
            Term::Lambda {
                name,
                parameter_type,
                body,
                ..
            } => (name, parameter_type, body),
            _ => panic!("{:#?}", lambda),
        }
    }

    fn codegen_function(
        &self,
        term: &Term,
        local: &mut local::Environment<'ctx>,
        configuration: &CodegenFunctionConfiguration,
    ) -> PointerValue<'ctx> {
        let (function_name, _parameter_type, function_body, lambda) = match configuration {
            CodegenFunctionConfiguration::Lambda => {
                let (name, parameter_type, body) =
                    Context::name_parameter_type_body_from_lambda(term);
                (name, parameter_type, body, term)
            }
            CodegenFunctionConfiguration::Fixpoint => match term {
                Term::Fixpoint { body: lambda, .. } => {
                    let (name, parameter_type, lambda_body) =
                        Context::name_parameter_type_body_from_lambda(lambda);
                    (name, parameter_type, lambda_body, &**lambda)
                }
                _ => panic!("{:#?}", term),
            },
            CodegenFunctionConfiguration::OuterConstructorFunction { .. } => {
                let (name, parameter_type, body) =
                    Context::name_parameter_type_body_from_lambda(term);
                (name, parameter_type, body, term)
            }
        };

        // if let Term::Sort(_) = parameter_type {
        //     if let CodegenFunctionConfiguration::OuterConstructorFunction = configuration {
        //         panic!("{:#?}", parameter_type)
        //     }
        //     return self.codegen_term_helper(function_body, local);
        // }

        // Get the indexes of all free variables in the lambda
        let free_debruijn_indexes = match configuration {
            CodegenFunctionConfiguration::Lambda
            | CodegenFunctionConfiguration::OuterConstructorFunction => {
                free_variables(&self.global, lambda, false)
            }
            CodegenFunctionConfiguration::Fixpoint => free_variables(&self.global, lambda, true),
        };

        let llvm_captures_struct_ptr = match configuration {
            CodegenFunctionConfiguration::Lambda | CodegenFunctionConfiguration::Fixpoint => {
                Some(self.codegen_capturing(&free_debruijn_indexes, local))
            }
            CodegenFunctionConfiguration::OuterConstructorFunction => None,
        };

        // Get the basic block that we were previously inserting instructions into. This is
        // used later to build the lambda struct.
        let llvm_previous_basic_block = self.builder.get_insert_block().unwrap();

        let llvm_function = self.initialize_function(
            &self.pointer_type(),
            match function_name {
                Name::Named(name) => name,
                Name::Anonymous => Self::anonymous_function_name(),
            },
        );

        if !free_debruijn_indexes.is_empty() {
            let casted_captures_struct_pointer = self
                .builder
                .build_bitcast(
                    llvm_function.get_nth_param(1).unwrap().into_pointer_value(),
                    llvm_captures_struct_ptr.unwrap().get_type(),
                    "casted_captures_struct_pointer",
                )
                .into_pointer_value();

            // Add captured values to the function and update the local environment
            for (i, free_debruijn_index) in free_debruijn_indexes.iter().enumerate() {
                let debruijn_stack_pointer = self
                    .builder
                    .build_alloca(self.pointer_type(), "debruijn_value");

                let debruijn_value_address = self
                    .builder
                    .build_struct_gep(
                        casted_captures_struct_pointer,
                        i.try_into().unwrap(),
                        &format!("captures_struct_field_{}_address", i),
                    )
                    .unwrap();
                let debruijn_value = self.builder.build_load(
                    debruijn_value_address,
                    &format!("captures_struct_field_{}_value", i),
                );

                self.builder
                    .build_store(debruijn_stack_pointer, debruijn_value);

                local.update_register_value_with_stack_pointer(
                    *free_debruijn_index,
                    debruijn_stack_pointer,
                );
            }
        }

        let llvm_lambda_function_ptr = llvm_function.as_global_value().as_pointer_value();

        if let CodegenFunctionConfiguration::Fixpoint = configuration {
            // Add the function to the local context
            local.push_recursive_function(free_debruijn_indexes, llvm_lambda_function_ptr);
        }

        // Push the parameter to the local environment.
        local.push_register_value(
            llvm_function
                .get_first_param()
                .unwrap()
                .into_pointer_value(),
        );

        // Codegen the body.
        let body_expression_value = self.codegen_term_helper(function_body, local);

        // Reset the local environment.
        local.pop();

        if let CodegenFunctionConfiguration::Fixpoint = configuration {
            // Remove the recursive function to the local context
            local.pop();
        }

        let casted_return_value = self.builder.build_bitcast(
            body_expression_value,
            self.pointer_type(),
            "return_i8_pointer",
        );

        // Return the result of the body.
        self.builder.build_return(Some(&casted_return_value));

        llvm_function.verify(true);

        // Set the builders back to the position it was at before codegening this lambda.
        self.builder.position_at_end(llvm_previous_basic_block);

        match configuration {
            CodegenFunctionConfiguration::OuterConstructorFunction { .. } => {
                llvm_lambda_function_ptr
            }
            _ => {
                // Return a pointer to the struct that represents this lambda.
                self.codegen_lambda_struct(
                    llvm_lambda_function_ptr,
                    llvm_captures_struct_ptr.unwrap(),
                )
            }
        }
    }

    fn codegen_lambda_struct(
        &self,
        llvm_lambda_function_ptr: PointerValue,
        llvm_captures_struct_ptr: PointerValue,
    ) -> PointerValue<'ctx> {
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
        let llvm_lambda_function_field_address = self
            .builder
            .build_struct_gep(
                llvm_lambda_struct_ptr,
                0,
                "lambda_struct_function_pointer_field_address",
            )
            .unwrap();
        self.builder
            .build_store(llvm_lambda_function_field_address, llvm_lambda_function_ptr);
        // Store `captures`
        let llvm_captures_field_address = self
            .builder
            .build_struct_gep(
                llvm_lambda_struct_ptr,
                1,
                "lambda_struct_captures_field_address",
            )
            .unwrap();
        self.builder
            .build_store(llvm_captures_field_address, llvm_captures_struct_ptr);

        llvm_lambda_struct_ptr
    }

    fn codegen_debruijn_index(
        &self,
        debruijn_index: DeBruijnIndex,
        local: &local::Environment<'ctx>,
    ) -> PointerValue<'ctx> {
        match local.lookup(debruijn_index) {
            DeBruijnValue::RegisterValue(pointer) => *pointer,
            DeBruijnValue::StackPointer(pointer) => self
                .builder
                .build_load(*pointer, "load_debruijn_stack_pointer")
                .into_pointer_value(),
            DeBruijnValue::RecursiveFunction {
                free_debruijn_indexes,
                function_pointer,
            } => {
                let captures_struct_pointer = self.codegen_capturing(free_debruijn_indexes, local);

                // Build the struct that represents this lambda and get a pointer to it.
                let lambda_struct_pointer =
                    self.codegen_lambda_struct(*function_pointer, captures_struct_pointer);

                self.builder
                    .build_bitcast(
                        lambda_struct_pointer,
                        self.pointer_type(),
                        "lambda_struct_pointer_cast",
                    )
                    .into_pointer_value()
            }
        }
    }

    fn codegen_exit_with_failure(&self) {
        let llvm_int_type = self.context.i32_type();
        self.builder.build_call(
            self.module.add_function(
                "exit",
                self.context
                    .void_type()
                    .fn_type(&[llvm_int_type.into()], false),
                Some(Linkage::External),
            ),
            &[llvm_int_type.const_int(1, false).into()],
            "exit_function_call",
        );
        self.builder.build_unreachable();
    }

    fn null_pointer(&self) -> PointerValue<'ctx> {
        self.pointer_type().const_null()
    }

    fn pointer_type(&self) -> PointerType<'ctx> {
        self.context.i8_type().ptr_type(AddressSpace::Generic)
    }

    fn function_pointer_type(&self) -> PointerType<'ctx> {
        self.pointer_type()
            .fn_type(
                &[self.pointer_type().into(), self.pointer_type().into()],
                false,
            )
            .ptr_type(AddressSpace::Generic)
    }

    fn function_struct_pointer_type(&self) -> PointerType<'ctx> {
        self.context
            .struct_type(
                &[
                    self.function_pointer_type().into(),
                    self.pointer_type().into(),
                ],
                false,
            )
            .ptr_type(AddressSpace::Generic)
    }

    fn constructor_parameter_count(struct_type: &StructType) -> usize {
        struct_type.get_field_types().len() - 1
    }

    fn codegen_pointer_to_empty_struct(&self) -> PointerValue<'ctx> {
        self.builder
            .build_malloc(self.context.struct_type(&[], false), "empty_struct")
            .unwrap()
    }

    fn anonymous_function_name() -> &'static str {
        "anonymous_lambda"
    }

    fn constructor_to_lambda_helper(
        inductive_name: &str,
        constructor_name: &str,
        constructor_index: u8,
        constructor_parameter_count: usize,
        constructor_parameters_left: usize,
    ) -> Term {
        if constructor_parameters_left <= 1 {
            Term::Lambda {
                name: Name::Named(Self::constructor_llvm_name(
                    inductive_name,
                    constructor_name,
                )),
                parameter_name: Name::Anonymous,
                parameter_type: Box::new(Term::Undefined(Undefined::Empty)),
                body: Box::new(Term::Undefined(
                    Undefined::CodegenInnerConstructorFunction {
                        constructor_index,
                        inductive_name: inductive_name.to_string(),
                        constructor_parameter_count,
                    },
                )),
            }
        } else {
            Term::Lambda {
                name: Name::Named(Self::constructor_llvm_name(
                    inductive_name,
                    constructor_name,
                )),
                parameter_name: Name::Anonymous,
                parameter_type: Box::new(Term::Undefined(Undefined::Empty)),
                body: Box::new(Context::constructor_to_lambda_helper(
                    inductive_name,
                    constructor_name,
                    constructor_index,
                    constructor_parameter_count,
                    constructor_parameters_left - 1,
                )),
            }
        }
    }

    fn constructor_to_lambda(
        inductive_name: &str,
        constructor_name: &str,
        constructor_index: u8,
        constructor_parameter_count: usize,
    ) -> Term {
        Self::constructor_to_lambda_helper(
            inductive_name,
            constructor_name,
            constructor_index,
            constructor_parameter_count,
            constructor_parameter_count,
        )
    }

    // Codegen llvm function for each constructor.
    fn codegen_constructor_function(
        &self,
        inductive_name: &str,
        constructor_name: &str,
        constructor_index: u8,
        constructor_llvm_struct_type: StructType<'ctx>,
    ) -> ConstructorFunction<'ctx> {
        let constructor_parameter_count =
            Context::constructor_parameter_count(&constructor_llvm_struct_type);
        let constructor_lambda_term = Context::constructor_to_lambda(
            inductive_name,
            constructor_name,
            constructor_index,
            constructor_parameter_count,
        );
        let llvm_constructor_function = self.codegen_function(
            &constructor_lambda_term,
            &mut local::Environment::new(),
            &CodegenFunctionConfiguration::OuterConstructorFunction,
        );

        if constructor_parameter_count == 0 {
            ConstructorFunction::ZeroArgumentFunctionPointer(llvm_constructor_function)
        } else {
            ConstructorFunction::FunctionPointer(llvm_constructor_function)
        }
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
            Term::DeBruijnIndex(_) => accumulator.push(self.pointer_type().into()),
            Term::Sort(_) => (),
            Term::DependentProduct {
                parameter_type,
                return_type,
                ..
            } => {
                self.codegen_constructor_type_helper(parameter_type, accumulator);
                self.codegen_constructor_type_helper(return_type, accumulator);
            }
            Term::Application { function, .. } => {
                self.codegen_constructor_type_helper(function, accumulator);
            }
            Term::Inductive(name) => {
                accumulator.push(self.global.lookup_inductive_llvm_type(name).into());
            }
            _ => unreachable!("{:#?}", constructor_type),
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
        let constructor_struct_type = self.codegen_constructor_type(
            &Self::constructor_llvm_name(inductive_name, &constructor.name),
            &constructor.typ,
        );

        self.global.add_constructor_struct_type(
            inductive_name,
            constructor.name.clone(),
            constructor_struct_type,
        );

        self.global.add_constructor_function(
            inductive_name,
            &constructor.name,
            self.codegen_constructor_function(
                inductive_name,
                &constructor.name,
                constructor_index,
                constructor_struct_type,
            ),
        );
    }

    fn codegen_inductive(&mut self, inductive: &Inductive) {
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
                let constructor_llvm_type = constructor.struct_type;
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

    pub fn codegen_fresh_inductive(&mut self, inductive: Inductive) {
        self.codegen_hir(&HIR {
            declarations: vec![Declaration::Inductive(inductive)],
        });
    }
}

#[cfg(test)]
mod tests {
    use inkwell::{types::BasicType, values::InstructionOpcode};

    use super::*;
    use crate::hir::examples;

    fn test_hir(hir: &HIR) {
        let inkwell_context = InkwellContext::create();
        let mut context = Context::build(&inkwell_context);
        context.codegen_hir(&hir);
        context.run_module();
    }

    fn test_hir_with_context<'ctx>(
        hir: &HIR,
        inkwell_context: &'ctx InkwellContext,
    ) -> Context<'ctx> {
        let mut context = Context::build(&inkwell_context);
        context.codegen_hir(&hir);
        context.run_module();
        context
    }

    fn test_inductive<'ctx>(
        inductive: Inductive,
        inkwell_context: &'ctx InkwellContext,
    ) -> Context<'ctx> {
        let mut context = Context::build(inkwell_context);
        context.codegen_hir(&HIR {
            declarations: vec![Declaration::Inductive(inductive)],
        });
        context.run_module();
        context
    }

    #[test]
    fn unit_type() {
        let unit = examples::unit();
        let inkwell_context = InkwellContext::create();
        let context = test_inductive(unit.clone(), &inkwell_context);

        let unit_llvm_struct = context.module.get_struct_type(&unit.name).unwrap();
        assert_eq!(unit_llvm_struct.get_field_types().len(), 0);
    }

    #[test]
    fn two_argument_constructor_type() {
        let hir = examples::two_argument_constructor();
        let inkwell_context = InkwellContext::create();
        let context = test_hir_with_context(&hir, &inkwell_context);
        let nat = hir.get_inductive(0);
        let tester = hir.get_inductive(1);
        let tester_constructor_llvm_name = &Context::constructor_llvm_name(
            &tester.name,
            &tester.constructors.get(0).unwrap().name,
        );

        let tester_llvm_struct = context.module.get_struct_type(&tester.name).unwrap();
        assert_eq!(tester_llvm_struct.get_field_types().len(), 3);

        let tester_constructor_llvm_struct = context
            .module
            .get_struct_type(tester_constructor_llvm_name)
            .unwrap();
        let constructor_field_types = tester_constructor_llvm_struct.get_field_types();
        assert_eq!(constructor_field_types.len(), 3);
        assert_eq!(
            constructor_field_types,
            tester_llvm_struct.get_field_types()
        );
        assert_eq!(
            constructor_field_types[0],
            context.context.i8_type().as_basic_type_enum()
        );
        let nat_field_type = context
            .module
            .get_struct_type(&nat.name)
            .unwrap()
            .ptr_type(AddressSpace::Generic)
            .as_basic_type_enum();
        assert_eq!(constructor_field_types[1], nat_field_type);
        assert_eq!(constructor_field_types[2], nat_field_type);

        context
            .module
            .get_function(tester_constructor_llvm_name)
            .unwrap();
        context
            .module
            .get_function(&format!("{}.1", tester_constructor_llvm_name))
            .unwrap();
    }

    #[test]
    fn nat_type() {
        let inductive_nat = examples::nat();
        let inkwell_context = InkwellContext::create();
        let context = test_inductive(inductive_nat.clone(), &inkwell_context);

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
    }

    #[test]
    fn nat_add() {
        test_hir(&examples::nat_add());
    }

    #[test]
    fn nat_identity() {
        test_hir(&examples::nat_identity());
    }

    #[test]
    fn nat_match_identity() {
        test_hir(&examples::nat_match_identity());
    }

    #[test]
    fn nat_match_simple() {
        test_hir(&examples::nat_match_simple());
    }

    #[test]
    fn nat_identity_global_constant_use_() {
        test_hir(&examples::global_constant_use_nat_identity());
    }

    #[test]
    fn nat_zero() {
        test_hir(&examples::nat_zero());
    }

    #[test]
    fn nat_one() {
        test_hir(&examples::nat_one());
    }

    #[test]
    fn nat_left() {
        let inkwell_context = InkwellContext::create();
        let context = test_hir_with_context(&examples::nat_left(), &inkwell_context);

        let inner_lambda = context
            .module
            .get_function(Context::anonymous_function_name())
            .unwrap();
        assert_eq!(inner_lambda.get_basic_blocks().len(), 1);
        let first_instruction = inner_lambda.get_basic_blocks()[0]
            .get_first_instruction()
            .unwrap();
        assert_eq!(first_instruction.get_opcode(), InstructionOpcode::BitCast);
        let next_instruction = first_instruction.get_next_instruction().unwrap();
        assert_eq!(next_instruction.get_opcode(), InstructionOpcode::Alloca);
        let next_instruction = next_instruction.get_next_instruction().unwrap();
        assert_eq!(
            next_instruction.get_opcode(),
            InstructionOpcode::GetElementPtr
        );
        let next_instruction = next_instruction.get_next_instruction().unwrap();
        assert_eq!(next_instruction.get_opcode(), InstructionOpcode::Load);
        let next_instruction = next_instruction.get_next_instruction().unwrap();
        assert_eq!(next_instruction.get_opcode(), InstructionOpcode::Store);
        let next_instruction = next_instruction.get_next_instruction().unwrap();
        assert_eq!(next_instruction.get_opcode(), InstructionOpcode::Load);
        let next_instruction = next_instruction.get_next_instruction().unwrap();
        assert_eq!(next_instruction.get_opcode(), InstructionOpcode::Return);
    }

    #[test]
    fn nat_to_zero() {
        test_hir(&examples::nat_to_zero());
    }

    #[test]
    fn list_type() {
        let list = examples::list();
        let inkwell_context = InkwellContext::create();
        let context = test_inductive(list.clone(), &inkwell_context);

        let list_llvm_struct = context.module.get_struct_type(&list.name).unwrap();
        assert_eq!(3, list_llvm_struct.get_field_types().len());

        let list_nil_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(
                &list.name,
                &list.constructors.get(0).unwrap().name,
            ))
            .unwrap();
        assert_eq!(1, list_nil_llvm_struct.get_field_types().len());
        assert_eq!(
            list_nil_llvm_struct.get_field_types()[0],
            context.context.i8_type().as_basic_type_enum()
        );

        let list_cons_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(
                &list.name,
                &list.constructors.get(1).unwrap().name,
            ))
            .unwrap();
        assert_eq!(3, list_cons_llvm_struct.get_field_types().len());
        assert_eq!(
            list_cons_llvm_struct.get_field_types()[0],
            context.context.i8_type().as_basic_type_enum()
        );
        assert_eq!(
            list_cons_llvm_struct.get_field_types()[1],
            context
                .context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()
        );
        assert_eq!(
            list_cons_llvm_struct.get_field_types()[2],
            list_llvm_struct
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()
        );
    }

    #[test]
    #[ignore]
    fn list_append() {
        let inkwell_context = InkwellContext::create();
        let context = test_hir_with_context(&examples::list_append(), &inkwell_context);

        context.module.get_function("list_append").unwrap();
        context
            .module
            .get_function(Context::anonymous_function_name())
            .unwrap();
        assert!(context
            .module
            .get_function(Context::anonymous_function_name())
            .is_none());
    }

    #[test]
    fn vector_type() {
        let vector_hir = examples::vector();
        let inkwell_context = InkwellContext::create();
        let context = test_hir_with_context(&vector_hir, &inkwell_context);

        let vector_inductive = match &vector_hir.declarations[1] {
            Declaration::Inductive(inductive) => inductive,
            _ => unreachable!(),
        };

        let vector_llvm_struct = context
            .module
            .get_struct_type(&vector_inductive.name)
            .unwrap();
        assert_eq!(4, vector_llvm_struct.get_field_types().len());

        let vector_nil_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(
                &vector_inductive.name,
                &vector_inductive.constructors.get(0).unwrap().name,
            ))
            .unwrap();
        assert_eq!(1, vector_nil_llvm_struct.get_field_types().len());
        assert_eq!(
            vector_nil_llvm_struct.get_field_types()[0],
            context.context.i8_type().as_basic_type_enum()
        );

        let vector_cons_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(
                &vector_inductive.name,
                &vector_inductive.constructors.get(1).unwrap().name,
            ))
            .unwrap();
        assert_eq!(4, vector_cons_llvm_struct.get_field_types().len());
        assert_eq!(
            vector_cons_llvm_struct.get_field_types()[0],
            context.context.i8_type().as_basic_type_enum()
        );
        assert_eq!(
            vector_cons_llvm_struct.get_field_types()[1],
            context
                .context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()
        );
        assert_eq!(
            vector_cons_llvm_struct.get_field_types()[2],
            context
                .module
                .get_struct_type(&vector_hir.get_inductive(0).name)
                .unwrap()
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()
        );
        assert_eq!(
            vector_cons_llvm_struct.get_field_types()[3],
            context
                .module
                .get_struct_type(&vector_hir.get_inductive(1).name)
                .unwrap()
                .ptr_type(AddressSpace::Generic)
                .as_basic_type_enum()
        );
    }

    #[test]
    #[ignore]
    fn vector_append() {
        test_hir(&examples::vector_append());
    }

    #[test]
    fn generate_constructor_lambda_term() {
        let empty_string = "".to_string();
        let empty_string_llvm_constructor =
            Context::constructor_llvm_name(&empty_string, &empty_string);
        assert_eq!(
            Context::constructor_to_lambda(&empty_string, &empty_string, 0, 1),
            Term::Lambda {
                name: Name::Named(empty_string_llvm_constructor.clone()),
                parameter_name: Name::Anonymous,
                parameter_type: Box::new(Term::Undefined(Undefined::Empty)),
                body: Box::new(Term::Undefined(
                    Undefined::CodegenInnerConstructorFunction {
                        constructor_index: 0,
                        inductive_name: empty_string.clone(),
                        constructor_parameter_count: 1
                    }
                ))
            }
        );
        assert_eq!(
            Context::constructor_to_lambda(&empty_string, &empty_string, 0, 2),
            Term::Lambda {
                name: Name::Named(empty_string_llvm_constructor.clone()),
                parameter_name: Name::Anonymous,
                parameter_type: Box::new(Term::Undefined(Undefined::Empty)),
                body: Box::new(Term::Lambda {
                    name: Name::Named(empty_string_llvm_constructor.clone()),
                    parameter_name: Name::Anonymous,
                    parameter_type: Box::new(Term::Undefined(Undefined::Empty)),
                    body: Box::new(Term::Undefined(
                        Undefined::CodegenInnerConstructorFunction {
                            constructor_index: 0,
                            inductive_name: empty_string,
                            constructor_parameter_count: 2
                        }
                    ))
                })
            }
        );
    }
}
