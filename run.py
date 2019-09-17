from cashproof.ops import prove_equivalence
from cashproof.parse_equiv_file import parse_equiv

import sys


def main():
    filename = sys.argv[1]
    src = open(filename, 'r').read()
    equivalences = parse_equiv(src)
    for equivalence in equivalences:
        left, right = equivalence
        result = prove_equivalence(left, right)
        if result is None:
            print(end='.')
        else:
            print()
            print('Equivalence FAILED:')
            print('Tried to prove:')
            print(' '.join(op.name if hasattr(op, 'name') else str(op) for op in left),
                  '<=>',
                  ' '.join(op.name if hasattr(op, 'name') else str(op) for op in right))
            print(result)
    print()


if __name__ == '__main__':
    main()
