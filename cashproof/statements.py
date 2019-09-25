from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Sequence, Union, List, Optional

import z3

Ast = Union[z3.Ast, bool]


class Statements(ABC):
    @abstractmethod
    def max_stackitem_size(self) -> int:
        pass

    @abstractmethod
    def assume(self, ast: Ast) -> 'Statements':
        pass

    @abstractmethod
    def verify(self, ast: Ast) -> 'Statements':
        pass

    @abstractmethod
    def assumed_statements(self) -> Sequence[Ast]:
        pass

    @abstractmethod
    def verify_statements(self) -> Sequence[Ast]:
        pass

    @abstractmethod
    def verify_opcode_indices(self) -> Sequence[int]:
        pass

    @abstractmethod
    def next_opcode(self) -> None:
        pass


@dataclass
class Stmts:
    statements: List[Ast]
    verify_statements: List[Ast]
    verify_opcode_indices: List[int]


@dataclass
class StmtIf:
    condition: Ast
    then: Stmts
    otherwise: Optional[Stmts]


class StatementsDefault(Statements):
    def __init__(self, max_stackitem_size) -> None:
        self._max_stackitem_size = max_stackitem_size
        self._current_stmts: Stmts = Stmts([], [], [])
        self._opcode_index = 0

    def max_stackitem_size(self) -> int:
        return self._max_stackitem_size

    def assume(self, ast: Ast) -> 'Statements':
        self._current_stmts.statements.append(ast)
        return self

    def verify(self, ast: Ast) -> 'Statements':
        self._current_stmts.verify_statements.append(ast)
        self._current_stmts.verify_opcode_indices.append(self._opcode_index)
        return self

    def assumed_statements(self) -> Sequence[Ast]:
        return list(self._current_stmts.statements)

    def verify_statements(self) -> Sequence[Ast]:
        return list(self._current_stmts.verify_statements)

    def next_opcode(self) -> None:
        self._opcode_index += 1

    def verify_opcode_indices(self) -> Sequence[int]:
        return list(self._current_stmts.verify_opcode_indices)
