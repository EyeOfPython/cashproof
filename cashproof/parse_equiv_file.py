from ast import literal_eval
from dataclasses import dataclass

from cashproof.opcodes import Opcode
import re

reg_num = re.compile('^-?\d+$')


@dataclass
class Equivalence:
    inverted: bool
    sides: list
    max_stackitem_size: int


def parse_equiv(src: str):
    src = ''.join(line for line in src.splitlines() if not line.strip().startswith('#'))

    equivalences = src.split(';')
    parsed_equivalences = []
    max_stackitem_size = 520
    for equivalence in equivalences:
        if not equivalence.strip():
            continue
        if equivalence.startswith('!'):
            if equivalence.startswith('!max_stackitem_size='):
                max_stackitem_size = int(equivalence[len('!max_stackitem_size='):])
                continue
        if '<=>' in equivalence:
            sides = equivalence.split('<=>')
            inverted = False
        elif '<!=>' in equivalence:
            sides = equivalence.split('<!=>')
            inverted = True
        else:
            print('invalid equivalence:', equivalence)
            quit()
            return
        sides = [[op for op in side.split()] for side in sides]
        parsed_sides = []
        for side in sides:
            ops = []
            for op in side:
                op = op.strip()
                if not op:
                    continue
                if reg_num.match(op) is not None:
                    ops.append(int(op))
                elif op.startswith('0x'):
                    ops.append(bytes.fromhex(op[2:]))
                elif op[:1] == '"' and op[-1:] == '"':
                    ops.append(literal_eval(op))
                elif op[:1] == "'" and op[-1:] == "'":
                    ops.append(literal_eval(op))
                else:
                    ops.append(Opcode[op])
            parsed_sides.append(ops)
        if parsed_sides:
            parsed_equivalences.append(Equivalence(inverted=inverted,
                                                   sides=parsed_sides,
                                                   max_stackitem_size=max_stackitem_size))
    return parsed_equivalences
