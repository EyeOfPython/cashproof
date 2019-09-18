from cashproof.func import Funcs
from cashproof.op import Op, OpVars, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.sort import SortBool
from cashproof.stack import VarNames, Stacks
from cashproof.statements import Statements


class OpAssumeBool(Op):
    def __init__(self, b: bool) -> None:
        self._bool = b

    def opcode(self) -> Opcode:
        return Opcode.OP_DROP

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        b = stack.pop(SortBool())
        return OpVarNames([b], [])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        b, = op_vars.inputs
        statements.assume(b == self._bool)
