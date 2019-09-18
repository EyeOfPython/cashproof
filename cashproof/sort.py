from abc import ABC, abstractmethod

import z3


class Sort(ABC):
    @abstractmethod
    def to_z3(self) -> z3.SortRef:
        pass

    @abstractmethod
    def to_c(self) -> str:
        pass


class _TypeEq:
    def __eq__(self, other):
        return type(self) == type(other)

    def __repr__(self) -> str:
        return type(self).__name__ + '()'


class SortInt(Sort, _TypeEq):
    def to_z3(self) -> z3.SortRef:
        return z3.BitVecSort(32)

    def to_c(self) -> str:
        return 'int'


class SortBool(Sort, _TypeEq):
    def to_z3(self) -> z3.SortRef:
        return z3.BoolSort()

    def to_c(self) -> str:
        return 'bool'


class SortString(Sort, _TypeEq):
    def to_z3(self) -> z3.SortRef:
        return z3.StringSort()

    def to_c(self) -> str:
        return 'string'


class SortUnknown(Sort, _TypeEq):
    def to_z3(self) -> z3.SortRef:
        return z3.DeclareSort('unknown')

    def to_c(self) -> str:
        return 'any'
