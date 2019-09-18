from cashproof.func import Funcs
from cashproof.op import Op, OpVars, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.sort import SortInt, SortBool
from cashproof.stack import VarNames, Stacks
from cashproof.statements import Statements


class OpNop(Op):
    def __init__(self, opcode: Opcode) -> None:
        self._opcode = opcode

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        return OpVarNames([], [])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        pass


class OpNopVerify(Op):
    def __init__(self, opcode: Opcode) -> None:
        self._opcode = opcode

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        in_val = stack.pop(SortInt())
        out_val = stack.push(var_names.new(), SortInt())
        return OpVarNames([in_val], [out_val])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        in_val, = op_vars.inputs
        out_val, = op_vars.outputs
        statements.assume(in_val == out_val)
        verify = funcs.define(f'{self._opcode.name}_FUNC', var_names, [SortInt()], SortBool(), [])
        statements.verify(verify(in_val))


NOPS = [
    OpNop(Opcode.OP_NOP),
    OpNop(Opcode.OP_NOP1),
    OpNopVerify(Opcode.OP_CHECKLOCKTIMEVERIFY),
    OpNopVerify(Opcode.OP_CHECKSEQUENCEVERIFY),
    OpNop(Opcode.OP_NOP4),
    OpNop(Opcode.OP_NOP5),
    OpNop(Opcode.OP_NOP6),
    OpNop(Opcode.OP_NOP7),
    OpNop(Opcode.OP_NOP8),
    OpNop(Opcode.OP_NOP9),
    OpNop(Opcode.OP_NOP10),
]
