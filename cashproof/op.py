from abc import ABC, abstractmethod
from typing import Sequence

import z3

from cashproof.func import Funcs, VarNames
from cashproof.opcodes import Opcode


class Stack(ABC):
    @abstractmethod
    def pop(self) -> z3.Ast:
        pass

    @abstractmethod
    def push(self, var: z3.Ast) -> None:
        pass

    @abstractmethod
    def alt_pop(self) -> z3.Ast:
        pass

    @abstractmethod
    def alt_push(self, var: z3.Ast) -> None:
        pass


class Op(ABC):
    @abstractmethod
    def opcode(self) -> Opcode:
        pass

    @abstractmethod
    def statements_apply(self, stack: Stack, funcs: Funcs, var_names: VarNames) -> Sequence[z3.Ast]:
        pass
