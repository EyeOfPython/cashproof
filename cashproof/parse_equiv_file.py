from ast import literal_eval
from dataclasses import dataclass
from typing import Sequence

from cashproof.opcodes import Opcode
import re

from cashproof.ops import If

reg_num = re.compile('^-?\d+$')


@dataclass
class Equivalence:
    inverted: bool
    sides: list
    max_stackitem_size: int


def parse_ops(raw_ops: Sequence[str], start: int, depth=0):
    ops = []
    i = start - 1
    while i + 1 < len(raw_ops):
        i += 1
        op = raw_ops[i]
        op = op.strip()
        if not op:
            continue
        if reg_num.match(op) is not None:
            ops.append(int(op))
        elif op == 'OP_IF' or op == 'OP_NOTIF':
            then, stop = parse_ops(raw_ops, i + 1, depth + 1)
            otherwise, stop = parse_ops(raw_ops, stop + 1, depth + 1)
            if op == 'OP_IF':
                ops.append(If(then, otherwise))
            else:
                ops.append(If(otherwise, then))
            if stop is None:
                raise ValueError()
            i = stop
        elif op == 'OP_ELSE' or op == 'OP_ENDIF':
            return ops, i
        elif op.startswith('0x'):
            ops.append(bytes.fromhex(op[2:]))
        elif op[:1] == '"' and op[-1:] == '"':
            ops.append(literal_eval(op))
        elif op[:1] == "'" and op[-1:] == "'":
            ops.append(literal_eval(op))
        else:
            ops.append(Opcode[op])
    return ops, None


def parse_equiv(src: str):
    src = ' '.join(line for line in src.splitlines() if not line.strip().startswith('#'))

    equivalences = src.split(';')
    parsed_equivalences = []
    max_stackitem_size = 520
    for equivalence in equivalences:
        equivalence = equivalence.strip()
        if not equivalence:
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
            ops, _ = parse_ops(side, 0)
            parsed_sides.append(ops)
        if parsed_sides:
            parsed_equivalences.append(Equivalence(inverted=inverted,
                                                   sides=parsed_sides,
                                                   max_stackitem_size=max_stackitem_size))
    return parsed_equivalences
