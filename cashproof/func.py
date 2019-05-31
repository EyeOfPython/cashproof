from abc import ABC, abstractmethod
from typing import Sequence, Callable, Dict

import z3

from cashproof.sort import Sort
from cashproof.stack import VarNames

Func = Callable[..., z3.Ast]


class FuncProperty(ABC):
    @abstractmethod
    def to_statement(self, func: z3.Ast, var_names: VarNames, input_sorts: Sequence[Sort]) -> z3.Ast:
        pass


class Funcs(ABC):
    @abstractmethod
    def define(self,
               name: str,
               var_names: VarNames,
               input_sorts: Sequence[Sort],
               output_sort: Sort,
               properties: Sequence[FuncProperty]) -> Func:
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
               output_sort: Sort,
               properties: Sequence[FuncProperty]) -> Func:
        if name in self._funcs:
            return self._funcs[name]
        func = z3.Function(name, *list(input_sorts) + [output_sort])
        self._funcs[name] = func
        for prop in properties:
            self._statements.append(prop.to_statement(func, var_names, input_sorts))

    def statements(self) -> Sequence[z3.Ast]:
        return self._statements


class Assoc(FuncProperty):
    def to_statement(self, func: Func, var_names: VarNames, input_sorts: Sequence[Sort]) -> z3.Ast:
        sort1, sort2 = input_sorts
        a = z3.Const(var_names.new('a'), sort1)
        b = z3.Const(var_names.new('b'), sort1)
        c = z3.Const(var_names.new('c'), sort2)
        return z3.ForAll((a, b, c), func(func(a, b), c) == func(a, func(b, c)))


class Commut(FuncProperty):
    def to_statement(self, func: Func, var_names: VarNames, input_sorts: Sequence[Sort]) -> z3.Ast:
        sort1, sort2 = input_sorts
        a = z3.Const(var_names.new('a'), sort1)
        b = z3.Const(var_names.new('b'), sort1)
        c = z3.Const(var_names.new('c'), sort2)
        return z3.ForAll((a, b, c), func(func(a, b), c) == func(a, func(b, c)))
