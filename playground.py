import z3

byte = z3.BitVecSort(7)

a = z3.Unit(z3.BitVecVal(10, byte))

print(a[0].sort())

