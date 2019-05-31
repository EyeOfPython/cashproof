from cashproof.cashproof_old import BuildAst, Funcs
from cashproof.opcodes import Opcode

funcs = Funcs()
build_a = BuildAst('a_', ['x', 'y'], funcs)
build_a.add_op(Opcode.OP_4)
build_a.add_op(Opcode.OP_CAT)
build_a.add_op(Opcode.OP_CAT)

build_b = BuildAst('b_', ['x', 'y'], funcs)
build_b.add_op(Opcode.OP_CAT)
build_b.add_op(Opcode.OP_4)
build_b.add_op(Opcode.OP_CAT)

build_a.prove_equivalence(build_b)
