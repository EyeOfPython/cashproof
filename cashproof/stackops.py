from abc import ABC, abstractmethod
from typing import Sequence

import z3

from cashproof.func import Funcs, VarNames
from cashproof.funcop import Stack
from cashproof.op import Op
from cashproof.opcodes import Opcode


class StackOp(ABC):
    @abstractmethod
    def apply(self, stack: Stack):
        pass


class StackOpMask(StackOp):
    def __init__(self, n_in: int, mask: Sequence[int]) -> None:
        self._n_in = n_in
        self._mask = mask

    def apply(self, stack: Stack):
        inputs = []
        for _ in range(self._n_in):
            inputs.append(stack.pop())
        for i in self._mask:
            stack.push(inputs[i])


class StackOpToAltStack(StackOp):
    def apply(self, stack: Stack):
        stack.alt_push(stack.pop())


class StackOpFromAltStack(StackOp):
    def apply(self, stack: Stack):
        stack.push(stack.alt_pop())


class OpStackOp(Op):
    def __init__(self, opcode: Opcode, stack_op: StackOp) -> None:
        self._opcode = opcode
        self._stack_op = stack_op

    def opcode(self) -> Opcode:
        return self._opcode

    def statements_apply(self, stack: Stack, funcs: Funcs, var_names: VarNames) -> Sequence[z3.Ast]:
        self._stack_op.apply(stack)
        return []
