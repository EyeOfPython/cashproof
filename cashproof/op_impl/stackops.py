from abc import ABC, abstractmethod
from typing import Sequence

import z3

from cashproof.func import Funcs
from cashproof.op import Op, OpVarNames, OpVars
from cashproof.opcodes import Opcode
from cashproof.stack import Stacks, VarNames
from cashproof.statements import Statements


class StackOp(ABC):
    @abstractmethod
    def apply(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        pass


class StackOpMask(StackOp):
    def __init__(self, n_in: int, mask: Sequence[int]) -> None:
        self._n_in = n_in
        self._mask = mask

    def apply(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        inputs = []
        outputs = []
        for _ in range(self._n_in):
            inputs.append(stack.pop(None))
        for i in self._mask:
            outputs.append(inputs[i])
            stack.push(inputs[i], None)
        return OpVarNames(list(reversed(inputs)), outputs)


class StackOpToAltStack(StackOp):
    def apply(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        top = stack.pop(None)
        stack.alt().push(top, None)
        return OpVarNames([top], [])


class StackOpFromAltStack(StackOp):
    def apply(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        return OpVarNames([], [stack.push(stack.alt().pop(None), None)])


class OpStackOp(Op):
    def __init__(self, opcode: Opcode, stack_op: StackOp) -> None:
        self._opcode = opcode
        self._stack_op = stack_op

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        return self._stack_op.apply(stack, var_names)

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        pass


class OpPick(Op):
    def __init__(self, idx: int) -> None:
        self._idx = idx

    def opcode(self) -> Opcode:
        return Opcode.OP_PICK

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        inputs = [stack.pop(None) for _ in range(self._idx + 1)]
        inputs_rev = list(reversed(inputs))
        outputs = inputs_rev + [inputs_rev[0]]
        for output in outputs:
            stack.push(output, None)
        return OpVarNames(inputs_rev, outputs)

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        pass

    def __repr__(self) -> str:
        return f'OpPick({self._idx})'


class OpRoll(Op):
    def __init__(self, idx: int) -> None:
        self._idx = idx

    def opcode(self) -> Opcode:
        return Opcode.OP_ROLL

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        inputs = [stack.pop(None) for _ in range(self._idx + 1)]
        inputs_rev = list(reversed(inputs))
        outputs = inputs_rev[1:] + [inputs_rev[0]]
        for output in outputs:
            stack.push(output, None)
        return OpVarNames(inputs_rev, outputs)

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        pass

    def __repr__(self) -> str:
        return f'OpRoll({self._idx})'


STACK_OPS = [
    OpStackOp(Opcode.OP_DROP,  StackOpMask(1, [])),
    OpStackOp(Opcode.OP_DUP,   StackOpMask(1, [0, 0])),
    OpStackOp(Opcode.OP_NIP,   StackOpMask(2, [0])),
    OpStackOp(Opcode.OP_OVER,  StackOpMask(2, [1, 0, 1])),
    OpStackOp(Opcode.OP_ROT,   StackOpMask(3, [1, 0, 2])),
    OpStackOp(Opcode.OP_SWAP,  StackOpMask(2, [0, 1])),
    OpStackOp(Opcode.OP_TUCK,  StackOpMask(2, [0, 1, 0])),
    OpStackOp(Opcode.OP_2DROP, StackOpMask(2, [])),
    OpStackOp(Opcode.OP_2DUP,  StackOpMask(2, [1, 0, 1, 0])),
    OpStackOp(Opcode.OP_3DUP,  StackOpMask(3, [2, 1, 0, 2, 1, 0])),
    OpStackOp(Opcode.OP_2OVER, StackOpMask(4, [3, 2, 1, 0, 3, 2])),
    OpStackOp(Opcode.OP_2ROT,  StackOpMask(6, [3, 2, 1, 0, 5, 4])),
    OpStackOp(Opcode.OP_2SWAP, StackOpMask(4, [1, 0, 3, 2])),
    OpStackOp(Opcode.OP_TOALTSTACK, StackOpToAltStack()),
    OpStackOp(Opcode.OP_FROMALTSTACK, StackOpFromAltStack()),
]
