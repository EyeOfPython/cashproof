from cashproof.func import Funcs, Assoc, Commut
from cashproof.funcop import OpFuncOp, FuncOpNAry
from cashproof.op import Op, OpVars, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.sort import SortString, SortBool
from cashproof.stack import Stacks, VarNames
from cashproof.statements import Statements


class OpEqual(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_EQUAL

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        b = stack.pop(None)
        a = stack.pop(None)
        equality = stack.push(var_names.new(f'({a}=={b})'), SortBool())
        return OpVarNames([a, b], [equality])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        a, b = op_vars.inputs
        equality, = op_vars.outputs
        statements.assume(equality == (a == b))


class OpEqualVerify(Op):
    def opcode(self) -> Opcode:
        return Opcode.OP_EQUALVERIFY

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        b = stack.pop(None)
        a = stack.pop(None)
        stack.add_equality(a, b)
        return OpVarNames([a, b], [])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        a, b = op_vars.inputs
        statements.verify(a == b)


BIT_LOGIC_OPS = [
    OpFuncOp(Opcode.OP_AND, FuncOpNAry('AND', [SortString(), SortString()], SortString(), [Assoc(), Commut()])),
    OpFuncOp(Opcode.OP_OR,  FuncOpNAry('OR',  [SortString(), SortString()], SortString(), [Assoc(), Commut()])),
    OpFuncOp(Opcode.OP_XOR, FuncOpNAry('XOR', [SortString(), SortString()], SortString(), [Assoc(), Commut()])),
    OpEqual(),
    OpEqualVerify(),
]
