from abc import ABC, abstractmethod
from typing import Sequence, Union

import z3

from cashproof.func import Sort, Funcs, FuncProperty, VarNames
from cashproof.op import Op, OpVars, Ast, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.stack import Stacks
from cashproof.statements import Statements


class FuncOp(ABC):
    @abstractmethod
    def input_sorts(self) -> Sequence[Sort]:
        pass

    @abstractmethod
    def output_sorts(self) -> Sequence[Sort]:
        pass

    @abstractmethod
    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        pass


class OpFuncOp(Op):
    def __init__(self, opcode: Opcode, func_op: FuncOp) -> None:
        self._opcode = opcode
        self._func_op = func_op

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        inputs = []
        outputs = []
        for input_sort in self._func_op.input_sorts():
            inputs.append(stack.pop(input_sort))
        for output_sort in self._func_op.output_sorts():
            outputs.append(stack.push(var_names.new(), output_sort))
        return OpVarNames(inputs, outputs)

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        self._func_op.statements(statements, op_vars, var_names, funcs)


class FuncOpNAry(FuncOp):
    def __init__(self,
                 func_name: Union[str, Sequence[str]],
                 input_sorts: Sequence[Sort],
                 output_sort: Union[Sort, Sequence[Sort]],
                 func_properties: Sequence[FuncProperty]=None) -> None:
        self._func_name = func_name
        self._input_sorts = input_sorts
        self._output_sorts = [output_sort] if isinstance(output_sort, Sort) else output_sort
        self._func_properties = func_properties or []

    def input_sorts(self) -> Sequence[Sort]:
        return self._input_sorts

    def output_sorts(self) -> Sequence[Sort]:
        return self._output_sorts

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        func_names = [self._func_name] if isinstance(self._func_name, str) else [self._func_name]
        for func_name, sort, outputs in zip(func_names, self._output_sorts, op_vars.outputs):
            func = funcs.define(self._func_name, var_names, self._input_sorts, sort, self._func_properties)
            statements.assume(outputs == func(*op_vars.inputs))
