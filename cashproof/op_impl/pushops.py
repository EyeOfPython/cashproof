import z3

from cashproof.func import Funcs
from cashproof.op import Op, OpVars, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.sort import SortInt, SortString, SortBool
from cashproof.stack import Stacks, VarNames
from cashproof.statements import Statements


class OpPushInt(Op):
    def __init__(self, opcode: Opcode, integer: int) -> None:
        self._opcode = opcode
        self._integer = integer

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        return OpVarNames([], [stack.push(var_names.new(), SortInt())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        result, = op_vars.outputs
        statements.assume(result == self._integer)


class OpPushString(Op):
    def __init__(self, opcode: Opcode, string: str) -> None:
        self._opcode = opcode
        self._string = string

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        return OpVarNames([], [stack.push(var_names.new(), SortString())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        result, = op_vars.outputs
        statements.assume(result == z3.StringVal(self._string))


class OpPushBool(Op):
    def __init__(self, opcode: Opcode, boolean: bool) -> None:
        self._opcode = opcode
        self._boolean = boolean

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        return OpVarNames([], [stack.push(var_names.new(), SortBool())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        result, = op_vars.outputs
        statements.assume(result == self._boolean)
