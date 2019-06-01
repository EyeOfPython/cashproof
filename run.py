from cashproof.ops import prove_equivalence
from examples import spedn_optimizations

for a, b in spedn_optimizations.optimizations:
    print('-----------------------------')
    print()
    print('proving:')
    print(a)
    print('==')
    print(b)
    prove_equivalence(a, b)

