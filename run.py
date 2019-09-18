from cashproof.ops import prove_equivalence, pretty_print_script
from cashproof.parse_equiv_file import parse_equiv

import sys


def main():
    filename = sys.argv[1]
    src = open(filename, 'r').read()
    equivalences = parse_equiv(src)
    for equivalence in equivalences:
        left, right = equivalence.sides
        result = prove_equivalence(left, right, equivalence.max_stackitem_size)
        if (result is None and not equivalence.inverted) or (result is not None and equivalence.inverted):
            print(end='.')
        else:
            print()
            print('Equivalence FAILED:')
            print('Tried to prove:')
            print(pretty_print_script(left), '<=>', pretty_print_script(right))
            print(result)
    print()


if __name__ == '__main__':
    main()
