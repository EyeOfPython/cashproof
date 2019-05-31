from abc import ABC, abstractmethod

import z3


class Sort(ABC):
    @abstractmethod
    def to_z3(self) -> z3.SortRef:
        pass


class _TypeEq:
    def __eq__(self, other):
        return type(self) == type(other)

    def __repr__(self) -> str:
        return type(self).__name__ + '()'


class SortInt(Sort, _TypeEq):
    def to_z3(self) -> z3.SortRef:
        return z3.BitVecSort(32)


class SortBool(Sort, _TypeEq):
    def to_z3(self) -> z3.SortRef:
        return z3.BoolSort()


class SortString(Sort, _TypeEq):
    def to_z3(self) -> z3.SortRef:
        return z3.StringSort()


class SortUnknown(Sort, _TypeEq):
    def to_z3(self) -> z3.SortRef:
        return z3.DeclareSort('unknown')
