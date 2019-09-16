from cashproof.opcodes import Opcode


def parse_equiv(src: str):
    src = ''.join(line for line in src.splitlines() if not line.strip().startswith('#'))

    equivalences = src.split(';')
    parsed_equivalences = []
    for equivalence in equivalences:
        sides = equivalence.split('<=>')
        sides = [[op for op in side.split()] for side in sides]
        parsed_sides = []
        for side in sides:
            ops = []
            for op in side:
                op = op.strip()
                if not op:
                    continue
                if op.isdigit():
                    ops.append(int(op))
                elif op[:1] == '"' and op[-1:] == '"':
                    ops.append(op[1:-1])
                else:
                    ops.append(Opcode[op])
            if ops:
                parsed_sides.append(ops)
        if parsed_sides:
            parsed_equivalences.append(parsed_sides)
    return parsed_equivalences
