from cashproof.cases import prove_equivalence_cases
from cashproof.ops import pretty_print_script
from cashproof.parse_equiv_file import parse_equiv

import sys


def main():
    filenames = sys.argv[1:]
    equivalences = []
    for filename in filenames:
        src = open(filename, 'r').read()
        equivalences.extend(parse_equiv(src))
    for equivalence in equivalences:
        left, right = equivalence.sides
        result = prove_equivalence_cases(left, right, equivalence.max_stackitem_size, equivalence.full_script)
        if (result is None and not equivalence.inverted) or (result is not None and equivalence.inverted):
            print(end='.')
        else:
            print()
            print('Equivalence FAILED:')
            print('Tried to prove:')
            print(pretty_print_script(left), '<=>', pretty_print_script(right))
            print('-'*80)
            print(result)
    print()


if __name__ == '__main__':
    main()
