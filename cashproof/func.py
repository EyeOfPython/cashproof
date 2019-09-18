from abc import ABC, abstractmethod
from typing import Sequence, Callable, Dict

import z3

from cashproof.sort import Sort
from cashproof.stack import VarNames

Func = Callable[..., z3.Ast]


class Funcs(ABC):
    @abstractmethod
    def define(self,
               name: str,
               var_names: VarNames,
               input_sorts: Sequence[Sort],
               output_sort: Sort) -> Func:
        pass

    @abstractmethod
    def statements(self) -> Sequence[z3.Ast]:
        pass


class FuncsDefault(Funcs):
    def __init__(self) -> None:
        self._funcs: Dict[str, z3.Function] = {}
        self._statements = []

    def define(self,
               name: str,
               var_names: VarNames,
               input_sorts: Sequence[Sort],
               output_sort: Sort) -> Func:
        if name in self._funcs:
            return self._funcs[name]
        func = z3.Function(name, *[input_sort.to_z3() for input_sort in input_sorts] + [output_sort.to_z3()])
        self._funcs[name] = func
        return func

    def statements(self) -> Sequence[z3.Ast]:
        return self._statements
