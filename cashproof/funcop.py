from abc import ABC, abstractmethod
from typing import Sequence, Union

import z3

from cashproof.func import Sort, Funcs, FuncProperty, VarNames
from cashproof.op import Op, Stack
from cashproof.opcodes import Opcode


class FuncOp(ABC):
    @abstractmethod
    def input_sorts(self) -> Sequence[Sort]:
        pass

    @abstractmethod
    def output_sorts(self) -> Sequence[Sort]:
        pass

    @abstractmethod
    def statements(self, inputs: Sequence[z3.Ast], outputs: Sequence[z3.Ast], funcs: Funcs) -> Sequence[z3.Ast]:
        pass


class OpFuncOp(Op):
    def __init__(self, opcode: Opcode, func_op: FuncOp) -> None:
        self._opcode = opcode
        self._func_op = func_op

    def opcode(self) -> Opcode:
        return self._opcode

    def statements_apply(self, stack: Stack, funcs: Funcs, var_names: VarNames) -> Sequence[z3.Ast]:
        inputs = []
        outputs = []
        for _ in self._func_op.input_sorts():
            inputs.append(stack.pop())
        for output_sort in self._func_op.output_sorts():
            outputs.append(z3.Const(var_names.new(), output_sort))
        return self._func_op.statements(inputs, outputs, funcs)


class SortInt(Sort):
    def to_z3(self) -> z3.Ast:
        return z3.IntSort()


class SortBool(Sort):
    def to_z3(self) -> z3.Ast:
        return z3.BoolSort()


class SortArray(Sort):
    def to_z3(self) -> z3.Ast:
        return z3.IntSort()


class FuncOpBinary(FuncOp):
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

    def statements(self, inputs: Sequence[z3.Ast], outputs: Sequence[z3.Ast], funcs: Funcs) -> Sequence[z3.Ast]:
        func_names = [self._func_name] if isinstance(self._func_name, str) else [self._func_name]
        statements = []
        for func_name, sort, outputs in zip(func_names, self._output_sorts, outputs):
            func = funcs.define(self._func_name, self._input_sorts, sort, self._func_properties)
            statements.append(outputs == func(*inputs))
        return statements
