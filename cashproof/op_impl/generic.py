from typing import Sequence, Callable

from cashproof.func import Funcs
from cashproof.op import Op, OpVars, Ast, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.sort import Sort
from cashproof.stack import VarNames, Stacks
from cashproof.statements import Statements


class OpGeneric(Op):
    def __init__(self,
                 opcode: Opcode,
                 input_sorts: Sequence[Sort],
                 output_sort: Sort,
                 func: Callable[..., Ast]) -> None:
        self._opcode = opcode
        self._input_sorts = input_sorts
        self._output_sorts = output_sort
        self._func = func

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        input_names = []
        for input_sort in self._input_sorts:
            input_names.append(stack.pop(input_sort))
        result = stack.push(var_names.new(), self._output_sorts)
        return OpVarNames(input_names, [result])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        result, = op_vars.outputs
        statements.assume(result == self._func(*op_vars.inputs))


class OpGenericVerify(Op):
    def __init__(self,
                 opcode: Opcode,
                 input_sorts: Sequence[Sort],
                 func: Callable[..., Ast]) -> None:
        self._opcode = opcode
        self._input_sorts = input_sorts
        self._func = func

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        input_names = []
        for input_sort in self._input_sorts:
            input_names.append(stack.pop(input_sort))
        return OpVarNames(input_names, [])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        statements.verify(self._func(*op_vars.inputs))
