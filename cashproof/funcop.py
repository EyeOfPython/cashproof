from abc import ABC, abstractmethod
from typing import Sequence

from cashproof.func import Sort, Funcs, VarNames
from cashproof.op import Op, OpVars, OpVarNames
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
