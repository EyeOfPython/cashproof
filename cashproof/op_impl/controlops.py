from cashproof.func import Funcs
from cashproof.op import Op, OpVars, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.sort import SortBool
from cashproof.stack import VarNames, Stacks
from cashproof.statements import Statements


class OpVerify(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_VERIFY

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        return OpVarNames([stack.pop(SortBool())], [])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        verify, = op_vars.inputs
        statements.verify(verify)


CONTROL_OPS = [
    OpVerify(),
]
