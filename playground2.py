# import z3
#
# byte = z3.BitVecSort(8)
#
# s1 = z3.StringVal(b'\0\0\0\0' b'\0\0\0\0')
# s2 = z3.String('s2')
#
# i = z3.Int('i')
#
# r = z3.Star(z3.Re('\0'))
#
# z3.prove(z3.InRe(s1, r))
#
#
# print(z3.Extract(4, 2, z3.BitVec('x', byte)).sort())
from cashproof.opcodes import Opcode
from cashproof.ops import prove_equivalence, If

prove_equivalence([
    Opcode.OP_CAT,
    Opcode.OP_CAT,
], [
    Opcode.OP_TOALTSTACK,
    Opcode.OP_CAT,
    Opcode.OP_FROMALTSTACK,
    #Opcode.OP_SWAP,
    Opcode.OP_CAT,
])

# prove_equivalence([
#     1,
#     Opcode.OP_EQUALVERIFY,
# ], [
#     0,
#     Opcode.OP_SWAP,
#     Opcode.OP_EQUALVERIFY,
# ])
