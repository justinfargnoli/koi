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
