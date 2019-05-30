from abc import ABC, abstractmethod
from typing import Sequence, Callable

import z3


Func = Callable[..., z3.Ast]


class VarNames(ABC):
    @abstractmethod
    def new(self, name: str=None) -> str:
        pass


class Sort(ABC):
    @abstractmethod
    def to_z3(self) -> z3.Ast:
        pass


class FuncProperty(ABC):
    @abstractmethod
    def to_statement(self, func: z3.Ast, var_names: VarNames, input_sorts: Sequence[Sort]) -> z3.Ast:
        pass


class Funcs(ABC):
    @abstractmethod
    def define(self,
               name: str,
               input_sorts: Sequence[Sort],
               output_sort: Sort,
               properties: Sequence[FuncProperty]) -> Func:
        pass


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
