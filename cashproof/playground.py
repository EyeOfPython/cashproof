import z3

a = z3.Int('a')
b = z3.Int('b')

z3.prove(a ** b > 0)
