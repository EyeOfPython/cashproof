from cashproof.func import Assoc
from cashproof.funcop import FuncOpBinary, SortArray, SortInt
from cashproof.opcodes import Opcode
from cashproof.stackops import StackOpMask, StackOpToAltStack, StackOpFromAltStack

stack_ops = {
    Opcode.OP_DROP:  StackOpMask(1, []),
    Opcode.OP_DUP:   StackOpMask(1, [0, 0]),
    Opcode.OP_NIP:   StackOpMask(2, [0]),
    Opcode.OP_OVER:  StackOpMask(2, [1, 0, 1]),
    Opcode.OP_ROT:   StackOpMask(3, [1, 0, 2]),
    Opcode.OP_SWAP:  StackOpMask(2, [0, 1]),
    Opcode.OP_TUCK:  StackOpMask(2, [0, 1, 0]),
    Opcode.OP_2DROP: StackOpMask(2, []),
    Opcode.OP_2DUP:  StackOpMask(1, [1, 0, 1, 0]),
    Opcode.OP_3DUP:  StackOpMask(3, [2, 1, 0, 2, 1, 0]),
    Opcode.OP_2OVER: StackOpMask(4, [3, 2, 1, 0, 3, 2]),
    Opcode.OP_2ROT:  StackOpMask(6, [3, 2, 1, 0, 5, 4]),
    Opcode.OP_2SWAP: StackOpMask(4, [1, 0, 3, 2]),
    Opcode.OP_TOALTSTACK: StackOpToAltStack(),
    Opcode.OP_FROMALTSTACK: StackOpFromAltStack(),
}

func_ops = {
    Opcode.OP_CAT:   FuncOpBinary('cat', [SortArray(), SortArray()], SortArray(), [Assoc()]),
    Opcode.OP_SPLIT: FuncOpBinary(['split_left', 'split_right'], [SortArray(), SortInt()], [SortArray(), SortArray()]),
}
