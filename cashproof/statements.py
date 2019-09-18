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


@dataclass
class Stmts:
    statements: List[Ast]
    verify_statements: List[Ast]


@dataclass
class StmtIf:
    condition: Ast
    then: Stmts
    otherwise: Optional[Stmts]


class StatementsDefault(Statements):
    def __init__(self, max_stackitem_size) -> None:
        self._max_stackitem_size = max_stackitem_size
        self._current_stmts: Stmts = Stmts([], [])

    def max_stackitem_size(self) -> int:
        return self._max_stackitem_size

    def assume(self, ast: Ast) -> 'Statements':
        self._current_stmts.statements.append(ast)
        return self

    def verify(self, ast: Ast) -> 'Statements':
        self._current_stmts.verify_statements.append(ast)
        return self

    def assumed_statements(self) -> Sequence[Ast]:
        return list(self._current_stmts.statements)

    def verify_statements(self) -> Sequence[Ast]:
        return list(self._current_stmts.verify_statements)
