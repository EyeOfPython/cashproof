from abc import ABC, abstractmethod
from typing import Sequence, Union, Any

import z3
from dataclasses import dataclass

from cashproof.func import Funcs
from cashproof.opcodes import Opcode
from cashproof.stack import Stacks, VarNames
from cashproof.statements import Statements


@dataclass
class OpVarNames:
    inputs: Sequence[str]
    outputs: Sequence[str]
    data: Any = None


@dataclass
class OpVars:
    inputs: Sequence[z3.Ast]
    outputs: Sequence[z3.Ast]
    data: Any


Ast = Union[z3.Ast, bool]


class Op(ABC):
    @abstractmethod
    def opcode(self) -> Opcode:
        pass

    @abstractmethod
    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        pass

    @abstractmethod
    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        pass
