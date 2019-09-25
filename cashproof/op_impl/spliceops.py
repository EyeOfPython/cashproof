import z3

from cashproof.func import Funcs
from cashproof.op import Op, OpVarNames, OpVars
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
        split_idx = stack.pop(SortInt())
        string = stack.pop(SortString())
        return OpVarNames(
            [split_idx, string],
            [stack.push(var_names.new(f'[{string},{split_idx}]_1'), SortString()),
             stack.push(var_names.new(f'[{string}_{split_idx}]_2'), SortString())],
        )

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        split_idx, string = op_vars.inputs
        result1, result2 = op_vars.outputs
        statements.assume(result1 == z3.SubString(string, 0, z3.BV2Int(split_idx)))
        statements.assume(result2 == z3.SubString(string, z3.BV2Int(split_idx), z3.Length(string)))


def _add_num_encode_assumptions(statements: Statements, num, abs_num, string, last_byte, sign_bit):
    zero_bit = z3.BitVecVal(0, 1)

    statements.assume(abs_num == z3.If(num < 0, -num, num))
    statements.assume(z3.If(z3.Length(string) > 0,
                            z3.Unit(last_byte) == z3.SubString(string, z3.Length(string) - 1, 1),
                            last_byte == 0))
    statements.assume(z3.If(num < 0, sign_bit == 1, sign_bit == 0))
    statements.assume(sign_bit == z3.Extract(7, 7, last_byte))

    statements.assume(z3.Implies(z3.Length(string) == 0, num == 0))
    statements.assume(z3.Implies(z3.Length(string) == 1, z3.And(
        string == z3.Unit(z3.Concat(sign_bit, z3.Extract(6, 0, abs_num))),
        abs_num <= 127,
    )))
    statements.assume(
        z3.Implies(z3.Length(string) == 2, z3.And(
            string[0] == z3.Unit(z3.Extract(7, 0, abs_num)),
            string[1] == z3.Unit(z3.Concat(sign_bit, z3.Extract(14, 8, abs_num))),
            abs_num <= 32767,
        ))
    )
    statements.assume(
        z3.Implies(z3.Length(string) == 3, z3.And(
            string[0] == z3.Unit(z3.Extract(7, 0, abs_num)),
            string[1] == z3.Unit(z3.Extract(15, 8, abs_num)),
            string[2] == z3.Unit(z3.Concat(sign_bit, z3.Extract(22, 16, abs_num))),
            abs_num <= 8388607,
        ))
    )
    statements.assume(
        z3.Implies(z3.Length(string) == 4, z3.And(
            string[0] == z3.Unit(z3.Extract(7, 0, abs_num)),
            string[1] == z3.Unit(z3.Extract(15, 8, abs_num)),
            string[2] == z3.Unit(z3.Extract(23, 16, abs_num)),
            string[3] == z3.Unit(z3.Concat(sign_bit, z3.Extract(30, 24, abs_num))),
            abs_num <= 2147483647,
        ))
    )
    statements.assume(
        z3.Implies(z3.Length(string) > 4, z3.And(
            string[0] == z3.Unit(z3.Extract(7, 0, abs_num)),
            string[1] == z3.Unit(z3.Extract(15, 8, abs_num)),
            string[2] == z3.Unit(z3.Extract(23, 16, abs_num)),
            string[3] == z3.Unit(z3.Concat(zero_bit, z3.Extract(30, 24, abs_num))),
            z3.InRe(z3.SubString(string, 4, z3.Length(string) - 5), z3.Star(z3.Re('\0'))),
            last_byte == z3.Concat(sign_bit, z3.BitVecVal(0, 7)),
            abs_num <= 2147483647,
        ))
    )


class OpNum2Bin(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_NUM2BIN

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        size = stack.pop(SortInt())
        num = stack.pop(SortInt())
        return OpVarNames([num, size], [stack.push(var_names.new(f'num2bin_{num}_{size}'), SortString())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        num, size = op_vars.inputs
        string, = op_vars.outputs
        statements.assume(z3.Length(string) == z3.BV2Int(size))

        abs_num = z3.Const(var_names.new(f'num2bin_abs_{num}_{size}'), SortInt().to_z3())
        last_byte = z3.Const(var_names.new(f'num2bin_last_byte_{num}_{size}'), z3.BitVecSort(8))
        sign_bit = z3.Const(var_names.new(f'num2bin_sign_{num}_{size}'), z3.BitVecSort(1))
        _add_num_encode_assumptions(statements, num, abs_num, string, last_byte, sign_bit)


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
        abs_num = z3.Const(var_names.new(f'bin2num_abs_{string}'), SortInt().to_z3())
        last_byte = z3.Const(var_names.new(f'bin2num_last_byte_{string}'), z3.BitVecSort(8))
        sign_bit = z3.Const(var_names.new(f'bin2num_sign_{string}'), z3.BitVecSort(1))
        _add_num_encode_assumptions(statements, num, abs_num, string, last_byte, sign_bit)


class OpSize(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_SIZE

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        string = stack.pop(SortString())
        return OpVarNames([string], [stack.push(var_names.new(f'size_{string}'), SortInt())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        string, = op_vars.inputs
        size, = op_vars.outputs
        statements.assume(z3.Length(string) == z3.BV2Int(size))


SPLICE_OPS = [
    OpCat(),
    OpSplit(),
    OpNum2Bin(),
    OpBin2Num(),
    OpSize(),
]
