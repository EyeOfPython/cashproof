from cashproof.opcodes import Opcode


optimizations = [
    ([Opcode.OP_CHECKSIG, Opcode.OP_VERIFY],         [Opcode.OP_CHECKSIGVERIFY]),
    ([3, Opcode.OP_CHECKMULTISIG, Opcode.OP_VERIFY], [3, Opcode.OP_CHECKMULTISIGVERIFY]),
    ([Opcode.OP_CHECKDATASIG, Opcode.OP_VERIFY],     [Opcode.OP_CHECKDATASIGVERIFY]),
    ([Opcode.OP_FALSE, Opcode.OP_EQUAL, Opcode.OP_NOT],
     [Opcode.OP_0NOTEQUAL]),
    ([Opcode.OP_EQUAL, Opcode.OP_VERIFY],            [Opcode.OP_EQUALVERIFY]),
    ([Opcode.OP_NUMEQUAL, Opcode.OP_VERIFY],         [Opcode.OP_NUMEQUALVERIFY]),
    # ([Opcode.OP_NOT, Opcode.OP_IF],                  [Opcode.OP_NOTIF]),
    ([Opcode.OP_FALSE, Opcode.OP_PICK],              [Opcode.OP_DUP]),
    ([Opcode.OP_TRUE, Opcode.OP_PICK],               [Opcode.OP_OVER]),
    ([Opcode.OP_OVER, Opcode.OP_OVER],               [Opcode.OP_2DUP]),
    ([Opcode.OP_TRUE, Opcode.OP_ADD],                [Opcode.OP_1ADD]),
    ([Opcode.OP_TRUE, Opcode.OP_SUB],                [Opcode.OP_1SUB]),
    ([2, Opcode.OP_PICK, 2, Opcode.OP_PICK, 2, Opcode.OP_PICK],
     [Opcode.OP_3DUP]),
    ([3, Opcode.OP_PICK, 3, Opcode.OP_PICK],         [Opcode.OP_2OVER]),
    ([Opcode.OP_DROP, Opcode.OP_DROP],               [Opcode.OP_2DROP]),
    ([2, Opcode.OP_ROLL],                            [Opcode.OP_ROT]),
]

for i in range(10):
    optimizations.append(
        ([i, Opcode.OP_PICK, i + 1, Opcode.OP_PICK],
         [i, Opcode.OP_PICK, Opcode.OP_DUP])
    )
