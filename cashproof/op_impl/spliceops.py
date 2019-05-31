from typing import Sequence

import z3

from cashproof.func import Funcs
from cashproof.op import Op, OpVarNames, OpVars, Ast
from cashproof.opcodes import Opcode
from cashproof.sort import SortString, SortInt
from cashproof.stack import Stacks, VarNames
from cashproof.statements import Statements


class OpCat(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_CAT

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        a = stack.pop(SortString())
        b = stack.pop(SortString())
        return OpVarNames([a, b], [stack.push(var_names.new(f'({a}+{b})'), SortString())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        a, b = op_vars.inputs
        result, = op_vars.outputs
        statements.assume(result == a + b)


class OpSplit(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_SPLIT

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        string = stack.pop(SortString())
        split_idx = stack.pop(SortInt())
        return OpVarNames(
            [string, split_idx],
            [stack.push(var_names.new(f'[{string},{split_idx}]_1'), SortString()),
             stack.push(var_names.new(f'[{string}_{split_idx}]_2'), SortString())],
        )

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        string, split_idx = op_vars.inputs
        result1, result2 = op_vars.outputs
        statements.assume(result1 == z3.SubString(string, 0, split_idx))
        statements.assume(result2 == z3.SubString(string, split_idx, z3.Length(string)))


class OpNum2Bin(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_NUM2BIN

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        num = stack.pop(SortInt())
        size = stack.pop(SortInt())
        return OpVarNames([num, size], [stack.push(var_names.new(f'num2bin_{num}_{size}'), SortString())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        num, size = op_vars.inputs
        result, = op_vars.outputs
        statements.assume(z3.Length(result) == z3.BV2Int(size))
        # TODO: not quite true (sign, minimal encoding etc)
        statements.assume(z3.SubString(result, 0, 1) == z3.Unit(z3.Extract(7, 0, num)))
        statements.assume(z3.SubString(result, 1, 1) == z3.Unit(z3.Extract(15, 8, num)))
        statements.assume(z3.SubString(result, 2, 1) == z3.Unit(z3.Extract(23, 16, num)))
        statements.assume(z3.SubString(result, 3, 1) == z3.Unit(z3.Extract(31, 24, num)))
        statements.assume(z3.InRe(z3.SubString(result, 4, z3.Length(result) - 4), z3.Star(z3.Re('\0'))))


class OpBin2Num(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_BIN2NUM

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        string = stack.pop(SortString())
        num = stack.push(var_names.new(f'bin2num_{string}'), SortInt())
        return OpVarNames([string], [num])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        string, = op_vars.inputs
        num, = op_vars.outputs
        statements.assume(z3.Length(string) >= 4,)
        # TODO: not quite true (sign, minimal encoding etc)
        statements.assume(z3.SubString(string, 0, 1) == z3.Unit(z3.Extract(7, 0, num)))
        statements.assume(z3.SubString(string, 1, 1) == z3.Unit(z3.Extract(15, 8, num)))
        statements.assume(z3.SubString(string, 2, 1) == z3.Unit(z3.Extract(23, 16, num)))
        statements.assume(z3.SubString(string, 3, 1) == z3.Unit(z3.Extract(31, 24, num)))


class OpSize(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_SIZE

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        string = stack.pop(SortString())
        return OpVarNames([string], [stack.push(var_names.new(f'size_{string}'), SortInt())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        string, = op_vars.inputs
        size, = op_vars.outputs
        statements.assume(z3.Length(string) == size)


SPLICE_OPS = [
    OpCat(),
    OpSplit(),
    OpNum2Bin(),
    OpBin2Num(),
    OpSize(),
]
