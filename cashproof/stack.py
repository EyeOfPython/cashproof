from abc import ABC, abstractmethod
from typing import List, Optional, Dict, Set

import z3

from cashproof.sort import Sort


class VarNames(ABC):
    @abstractmethod
    def new(self, name: str=None) -> str:
        pass

    @abstractmethod
    def glob(self, name: str) -> str:
        pass


class Stack(ABC):
    @abstractmethod
    def pop(self, expected_sort: Optional[Sort]) -> str:
        pass

    @abstractmethod
    def push(self, var_name: str, sort: Optional[Sort]) -> str:
        pass

    @abstractmethod
    def depth(self) -> int:
        pass

    @abstractmethod
    def add_equality(self, a: str, b: str) -> None:
        pass

    @abstractmethod
    def copy(self) -> 'Stack':
        pass

    @abstractmethod
    def solve_all(self) -> Dict[str, Sort]:
        pass

    @abstractmethod
    def input_var_names(self) -> List[str]:
        pass

    @abstractmethod
    def output_var_names(self) -> List[str]:
        pass


class Stacks(Stack):
    def __init__(self, stack: Stack, alt_stack: Stack) -> None:
        self._stack = stack
        self._alt_stack = alt_stack

    def pop(self, expected_sort: Optional[Sort]) -> str:
        return self._stack.pop(expected_sort)

    def push(self, var_name: str, sort: Optional[Sort]) -> str:
        return self._stack.push(var_name, sort)

    def depth(self) -> int:
        return self._stack.depth()

    def stack(self) -> Stack:
        return self._stack

    def alt(self) -> Stack:
        return self._alt_stack

    def add_equality(self, a: str, b: str) -> None:
        return self._stack.add_equality(a, b)

    def copy(self) -> 'Stacks':
        return Stacks(self._stack.copy(), self._alt_stack.copy())

    def solve_all(self) -> Dict[str, Sort]:
        return self._stack.solve_all()

    def input_var_names(self) -> List[str]:
        return self._stack.input_var_names()

    def output_var_names(self) -> List[str]:
        return self._stack.output_var_names()


class StackStrict(Stack):
    def __init__(self, input_var_gen: VarNames) -> None:
        self._var_sorts: Dict[str, Sort] = {}
        self._equalities: Dict[str, Set[str]] = {}
        self._var_names: List[str] = []
        self._input_var_names: List[str] = []
        self._input_var_gen = input_var_gen

    def pop(self, expected_sort: Optional[Sort]) -> str:
        if not self._var_names:
            name = self._input_var_gen.new(f'input_{len(self._input_var_names)}')
            if expected_sort is not None:
                self._set_sort(name, expected_sort)
            self._input_var_names.append(name)
            return name
        else:
            top = self._var_names.pop()
            if expected_sort is not None:
                self._set_sort(top, expected_sort)
            return top

    def _set_sort(self, var_name: str, sort: Sort):
        if var_name in self._var_sorts and self._var_sorts[var_name] != sort:
            raise ValueError(f'Inconsistent sorts for {var_name}: {self._var_sorts[var_name]} != {sort}')
        self._var_sorts[var_name] = sort

    def add_equality(self, a: str, b: str) -> None:
        self._equalities.setdefault(a, set()).add(b)
        self._equalities.setdefault(b, set()).add(a)

    def solve_all(self) -> Dict[str, Sort]:
        while True:
            intersection = self._equalities.keys() & self._var_sorts.keys()
            if not intersection:
                if not self._equalities:
                    return self._var_sorts
                else:
                    print(f'Note: could not solve all sorts: {self._equalities}')
                    return self._var_sorts
            for a in intersection:
                equals = self._equalities[a]
                sort = self._var_sorts[a]
                for b in equals:
                    self._set_sort(b, sort)
                del self._equalities[a]

    def push(self, var_name: str, sort: Optional[Sort]) -> str:
        self._var_names.append(var_name)
        if sort is not None:
            self._set_sort(var_name, sort)
        return var_name

    def depth(self) -> int:
        return len(self._var_names)

    def input_var_names(self) -> List[str]:
        return self._input_var_names

    def output_var_names(self) -> List[str]:
        return self._var_names

    def copy(self) -> 'Stack':
        new = StackStrict(self._input_var_gen)
        new._var_sorts = self._var_sorts.copy()
        new._equalities = {k: v.copy() for k, v in self._equalities.items()}
        new._var_names = self._var_names.copy()
        new._input_var_names = self._input_var_names.copy()
        return new


class VarNamesIdentity(VarNames):
    counter = 0

    def new(self, name: str = None) -> str:
        if name is not None:
            return name
        else:
            VarNamesIdentity.counter += 1
            return f'v{VarNamesIdentity.counter}'

    def glob(self, name: str) -> str:
        return name


class VarNamesPrefix(VarNames):
    def __init__(self, prefix: str, var_names: VarNames) -> None:
        self._prefix = prefix
        self._var_names = var_names

    def new(self, name: str = None) -> str:
        name = self._var_names.new(name)
        return f'{self._prefix}{name}'

    def glob(self, name: str) -> str:
        return self._var_names.glob(name)


def test_stack():
    from cashproof.sort import SortInt
    stack = StackStrict(VarNamesIdentity())
    a = stack.pop(None)
    b = stack.pop(None)
    c = stack.pop(None)
    d = stack.pop(None)
    stack.push(d, SortInt())
    stack.add_equality(a, b)
    #stack.add_equality(b, c)
    stack.add_equality(c, d)
    stack.solve_all()
    print(stack._var_sorts)


if __name__ == '__main__':
    import sys
    sys.path.insert(0, '..')
    test_stack()
