use crate::hir::ir::{Declaration, Inductive, Term, HIR};
use environment::local;
use inkwell::{
    builder::Builder,
    context::Context as InkwellContext,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, PointerType, StructType},
    values::{BasicValue, BasicValueEnum},
    AddressSpace,
};

mod environment {
    pub mod local {
        use crate::hir::ir::DeBruijnIndex;
        use inkwell::values::BasicValueEnum;

        pub struct Environment<'ctx> {
            debruijn_values: Vec<BasicValueEnum<'ctx>>,
        }

        impl<'ctx> Environment<'ctx> {
            pub fn new() -> Environment<'ctx> {
                Environment {
                    debruijn_values: Vec::new(),
                }
            }

            pub fn push(&mut self, value: BasicValueEnum<'ctx>) {
                self.debruijn_values.push(value)
            }

            pub fn pop(&mut self) {
                self.debruijn_values.pop().unwrap();
            }

            pub fn lookup(&self, debruijn_index: DeBruijnIndex) -> &BasicValueEnum<'ctx> {
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

            fn lookup_inductive(&self, name: &str) -> &Inductive<'ctx> {
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

        struct Inductive<'ctx> {
            name: Identifier,
            llvm_type: PointerType<'ctx>,
            constructors: Vec<Constructor<'ctx>>,
        }

        pub struct Constructor<'ctx> {
            name: Identifier,
            llvm_type: PointerType<'ctx>,
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
        self.codegen_term_helper(term, &mut local::Environment::new());
    }

    fn llvm_pointer_type(&self) -> PointerType<'ctx> {
        self.context.i8_type().ptr_type(AddressSpace::Generic)
    }

    fn codegen_term_helper(
        &mut self,
        term: &Term,
        local: &mut local::Environment<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        match term {
            Term::DeBruijnIndex(debruijn_index) => local.lookup(*debruijn_index).clone(),
            Term::Lambda {
                parameter_name,
                body,
                ..
            } => {
                let llvm_lambda_function_type = self.llvm_pointer_type().fn_type(
                    &[BasicMetadataTypeEnum::from(self.llvm_pointer_type())],
                    false,
                );

                // let llvm_lambda_function_pointer_type =
                //     llvm_lambda_function_type.ptr_type(AddressSpace::Generic);
                // let lambda_struct = self.context.struct_type(
                //     &[llvm_lambda_function_pointer_type.as_basic_type_enum()],
                //     false,
                // );

                let llvm_lambda_function_value =
                    self.module
                        .add_function("", llvm_lambda_function_type, None);

                local.push(llvm_lambda_function_value.get_first_param().unwrap());

                let llvm_function_entry_basic_block = self
                    .context
                    .append_basic_block(llvm_lambda_function_value, "");
                self.builder
                    .position_at_end(llvm_function_entry_basic_block);

                let return_value = self.codegen_term_helper(body, local);

                local.pop();

                self.builder.build_return(Some(&return_value));

                llvm_lambda_function_value.verify(true);

                llvm_lambda_function_value
                    .as_global_value()
                    .as_pointer_value()
                    .as_basic_value_enum()
            }
            _ => todo!("{:#?}", term),
        }
    }

    pub fn constructor_llvm_name(inductive_name: &str, constructor_name: &str) -> String {
        format!("{}_{}", inductive_name, constructor_name)
    }

    fn codegen_constructor_type(&self, constructor_type: &Term) -> Vec<BasicTypeEnum> {
        match constructor_type {
            Term::Inductive(name, _) => {
                vec![self
                    .global
                    .lookup_inductive_llvm_type(&name)
                    .as_basic_type_enum()]
            }
            Term::DependentProduct {
                parameter_name: _,
                parameter_type,
                return_type,
            } => {
                let mut field_types = self.codegen_constructor_type(&parameter_type);
                field_types.append(&mut self.codegen_constructor_type(&return_type));
                field_types
            }
            _ => panic!(),
        }
    }

    pub fn codegen_inductive(&mut self, inductive: &Inductive) {
        let inductive_llvm_struct_type = self.context.opaque_struct_type(&inductive.name);

        self.global.push_inductive(
            inductive.name.clone(),
            inductive_llvm_struct_type.ptr_type(AddressSpace::Generic),
        );

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
    fn nat() {
        let inductive_nat = &examples::nat();
        let natural = "Natural".to_string();
        let zero = "Zero".to_string();
        let successor = "Successor".to_string();

        let inkwell_context = InkwellContext::create();
        let mut context = Context::build(&inkwell_context);
        context.codegen_inductive(inductive_nat);

        let nat_llvm_struct = context.module.get_struct_type(&natural).unwrap();
        let nat_field_types = nat_llvm_struct.get_field_types();
        assert_eq!(nat_field_types.len(), 2);

        let nat_llvm_ptr = context
            .global
            .lookup_inductive_llvm_type(&natural)
            .as_basic_type_enum();

        let nat_zero_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(&natural, &zero))
            .unwrap();
        let zero_field_types = nat_zero_llvm_struct.get_field_types();
        assert_eq!(zero_field_types.len(), 1);
        assert_eq!(zero_field_types[0], nat_llvm_ptr);

        let nat_successor_llvm_struct = context
            .module
            .get_struct_type(&Context::constructor_llvm_name(&natural, &successor))
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

        let llvm_identity_function = context.module.get_first_function().unwrap();

        let llvm_first_parameter = llvm_identity_function.get_first_param().unwrap();
        let llvm_first_parameter_pointer = llvm_first_parameter.into_pointer_value();
        assert_eq!(
            llvm_first_parameter_pointer
                .get_type()
                .get_element_type()
                .into_int_type(),
            context.context.i8_type()
        );

        let llvm_basic_blocks = llvm_identity_function.get_basic_blocks();
        assert_eq!(llvm_basic_blocks.len(), 1);

        let llvm_first_basic_block = llvm_basic_blocks.get(0).unwrap();
        assert_eq!(
            llvm_first_basic_block.get_first_instruction(),
            llvm_first_basic_block.get_last_instruction()
        );
    }
}
