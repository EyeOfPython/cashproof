from typing import Callable

from cashproof.func import Funcs
from cashproof.op import Op, OpVars, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.sort import SortString, SortBool
from cashproof.stack import Stacks, VarNames
from cashproof.statements import Statements

import z3


class OpEqual(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_EQUAL

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        b = stack.pop(None)
        a = stack.pop(None)
        equality = stack.push(var_names.new(f'({a}=={b})'), SortBool())
        stack.add_sort_equality(a, b)
        return OpVarNames([a, b], [equality])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        a, b = op_vars.inputs
        equality, = op_vars.outputs
        statements.assume(equality == (a == b))


class OpEqualVerify(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_EQUALVERIFY

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        b = stack.pop(None)
        a = stack.pop(None)
        stack.add_sort_equality(a, b)
        return OpVarNames([a, b], [])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        a, b = op_vars.inputs
        statements.verify(a == b)


class OpBitLogic(Op):
    def __init__(self, opcode: Opcode, func: Callable) -> None:
        self._opcode = opcode
        self._func = func

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        b = stack.pop(SortString())
        a = stack.pop(SortString())
        result = stack.push(var_names.new(f'bitop({a},{b})'), SortString())
        return OpVarNames([a, b], [result])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        a, b = op_vars.inputs
        result, = op_vars.outputs
        statements.assume(z3.Length(result) == z3.Length(b))
        statements.assume(z3.Length(result) == z3.Length(a))
        for i in range(0, statements.max_stackitem_size()):
            a_i = z3.BitVec(var_names.new(f'bitop_a{i}({a},{b})'), 8)
            b_i = z3.BitVec(var_names.new(f'bitop_b{i}({a},{b})'), 8)
            statements.assume(z3.Implies(
                i < z3.Length(result),
                z3.And(
                    result[i] == z3.Unit(self._func(a_i, b_i)),
                    a[i] == z3.Unit(a_i),
                    b[i] == z3.Unit(b_i),
                ),
            ))


BIT_LOGIC_OPS = [
    OpBitLogic(Opcode.OP_AND, lambda a, b: a & b),
    OpBitLogic(Opcode.OP_OR, lambda a, b: a | b),
    OpBitLogic(Opcode.OP_XOR, lambda a, b: a ^ b),
    OpEqual(),
    OpEqualVerify(),
]
