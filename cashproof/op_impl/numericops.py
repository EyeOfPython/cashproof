import z3

from cashproof.op_impl.generic import OpGeneric, OpGenericVerify
from cashproof.opcodes import Opcode
from cashproof.sort import SortInt, SortBool


NUMERIC_OPS = [
    OpGeneric(Opcode.OP_1ADD,      [SortInt()],  SortInt(), lambda x: x + 1),
    OpGeneric(Opcode.OP_1SUB,      [SortInt()],  SortInt(), lambda x: x - 1),

    OpGeneric(Opcode.OP_NEGATE,    [SortInt()],  SortInt(), lambda x: -x),
    OpGeneric(Opcode.OP_ABS,       [SortInt()],  SortInt(), lambda x: z3.If(x > 0, x, -x)),
    OpGeneric(Opcode.OP_NOT,       [SortBool()], SortBool(), lambda x: z3.Not(x)),
    OpGeneric(Opcode.OP_0NOTEQUAL, [SortInt()],  SortBool(), lambda x: x != 0),

    OpGeneric(Opcode.OP_ADD, [SortInt(), SortInt()], SortInt(), lambda a, b: a + b),
    OpGeneric(Opcode.OP_SUB, [SortInt(), SortInt()], SortInt(), lambda a, b: a - b),
    # OpGeneric(Opcode.OP_MUL, lambda a, b: a * b),
    OpGeneric(Opcode.OP_DIV, [SortInt(), SortInt()], SortInt(), lambda a, b: a / b),
    OpGeneric(Opcode.OP_MOD, [SortInt(), SortInt()], SortInt(), lambda a, b: a % b),

    OpGenericVerify(Opcode.OP_NUMEQUALVERIFY, [SortInt(), SortInt()], lambda a, b: a == b),
    OpGeneric(Opcode.OP_BOOLAND,            [SortBool(), SortBool()], SortBool(), lambda a, b: z3.And(a, b)),
    OpGeneric(Opcode.OP_BOOLOR,             [SortBool(), SortBool()], SortBool(), lambda a, b: z3.Or(a, b)),
    OpGeneric(Opcode.OP_NUMEQUAL,           [SortInt(), SortInt()],   SortBool(), lambda a, b: a == b),
    OpGeneric(Opcode.OP_NUMNOTEQUAL,        [SortInt(), SortInt()],   SortBool(), lambda a, b: a != b),
    OpGeneric(Opcode.OP_LESSTHAN,           [SortInt(), SortInt()],   SortBool(), lambda a, b: a < b),
    OpGeneric(Opcode.OP_LESSTHANOREQUAL,    [SortInt(), SortInt()],   SortBool(), lambda a, b: a <= b),
    OpGeneric(Opcode.OP_GREATERTHAN,        [SortInt(), SortInt()],   SortBool(), lambda a, b: a > b),
    OpGeneric(Opcode.OP_GREATERTHANOREQUAL, [SortInt(), SortInt()],   SortBool(), lambda a, b: a >= b),
    OpGeneric(Opcode.OP_MIN,                [SortInt(), SortInt()],   SortInt(), lambda a, b: z3.If(a > b, b, a)),
    OpGeneric(Opcode.OP_MAX,                [SortInt(), SortInt()],   SortInt(), lambda a, b: z3.If(a > b, a, b)),
    OpGeneric(Opcode.OP_WITHIN, [SortInt(), SortInt(), SortInt()],    SortBool(),
              lambda x, lower, upper: z3.And(x >= lower, x < upper)),
]
