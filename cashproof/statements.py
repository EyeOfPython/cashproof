from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Sequence, Union, List, Optional

import z3

Ast = Union[z3.Ast, bool]


class Statements(ABC):
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
    def begin_if(self, condition: Ast):
        pass

    @abstractmethod
    def begin_else(self):
        pass

    @abstractmethod
    def end_if(self):
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
    def __init__(self) -> None:
        self._current_stmts: Stmts = Stmts([], [])
        self._initial_stmts = self._current_stmts
        self._branch_stack: List[StmtIf] = []
        self._branches: List[StmtIf] = []

    def assume(self, ast: Ast) -> 'Statements':
        self._current_stmts.statements.append(ast)
        return self

    def verify(self, ast: Ast) -> 'Statements':
        self._current_stmts.verify_statements.append(ast)
        return self

    def assumed_statements(self) -> Sequence[Ast]:
        if self._branch_stack:
            raise ValueError("Unclosed OP_IF (this is a bug)")
        return [
            z3.If(branch.condition, z3.And(*branch.then.statements), z3.And(*branch.otherwise.statements))
            for branch in self._branches
        ] + list(self._initial_stmts.statements)

    def verify_statements(self) -> Sequence[Ast]:
        if self._branch_stack:
            raise ValueError("Unclosed OP_IF (this is a bug)")
        return [
            z3.If(branch.condition, branch.then.verify_statements, branch.otherwise.verify_statements)
            for branch in self._branches
        ] + list(self._initial_stmts.verify_statements)

    def begin_if(self, condition: Ast):
        self._current_stmts = Stmts([], [])
        self._branch_stack.append(
            StmtIf(
                z3.And(condition, *[stmt_if.condition for stmt_if in self._branch_stack]),
                self._current_stmts,
                None,
            )
        )

    def begin_else(self):
        self._current_stmts = Stmts([], [])
        self._branch_stack[-1].otherwise = self._current_stmts

    def end_if(self):
        self._branches.append(self._branch_stack.pop())
        if self._branch_stack:
            top = self._branch_stack[-1]
            if top.otherwise is not None:
                self._current_stmts = top.otherwise
            else:
                self._current_stmts = top.then
        else:
            self._current_stmts = self._initial_stmts
