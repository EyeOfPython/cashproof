from ast import literal_eval
from dataclasses import dataclass
from typing import Sequence, Union, Tuple, Optional, TextIO
from io import StringIO

import z3

from cashproof.func import Funcs, FuncsDefault
from cashproof.op import Op, OpVars
from cashproof.op_impl.assume import OpAssumeBool
from cashproof.op_impl.bitlogicops import BIT_LOGIC_OPS
from cashproof.op_impl.controlops import CONTROL_OPS
from cashproof.op_impl.cryptoops import CRYPTO_OPS, OpCheckMultiSig
from cashproof.op_impl.nop import NOPS
from cashproof.op_impl.numericops import NUMERIC_OPS
from cashproof.op_impl.pushops import OpPushInt, OpPushString, OpPushBool
from cashproof.op_impl.spliceops import SPLICE_OPS
from cashproof.op_impl.stackops import STACK_OPS, OpPick, OpRoll
from cashproof.opcodes import Opcode
from cashproof.sort import Sort, SortUnknown, SortBool
from cashproof.stack import Stacks, StackStrict, VarNamesIdentity, VarNames, VarNamesPrefix
from cashproof.statements import StatementsDefault, Statements

OPS = {
    op.opcode(): op
    for op in STACK_OPS + SPLICE_OPS + CONTROL_OPS + BIT_LOGIC_OPS + NUMERIC_OPS + CRYPTO_OPS + NOPS
}


ScriptItem = Union[Opcode, int, str, bytes, bool, 'If', 'AssumeBool']


@dataclass
class If:
    then: Sequence[ScriptItem]
    otherwise: Sequence[ScriptItem]


@dataclass
class AssumeBool:
    top: bool


@dataclass
class TransformedOps:
    conditions: Sequence[Tuple[str, bool]]
    expected_inputs: Sequence[z3.Ast]
    expected_input_names: Sequence[str]
    expected_input_sorts: Sequence[Sort]
    outputs: Sequence[z3.Ast]
    output_sorts: Sequence[Sort]


def parse_int_op(opcode: Opcode) -> Optional[int]:
    if Opcode.OP_1NEGATE == opcode:
        return -1
    if Opcode.OP_0 == opcode:
        return 0
    if Opcode.OP_1.value <= opcode.value <= Opcode.OP_16.value:
        return opcode.value - Opcode.OP_1.value + 1
    return None


def parse_script_item(script_item: ScriptItem, max_stackitem_size: int) -> Op:
    if isinstance(script_item, Opcode):
        parsed_int = parse_int_op(script_item)
        if parsed_int is not None:
            return OpPushInt(..., parsed_int)
        return OPS[script_item]
    elif isinstance(script_item, bool):
        return OpPushBool(script_item, script_item)
    elif isinstance(script_item, int):
        return OpPushInt(script_item, script_item)
    elif isinstance(script_item, (str, bytes)):
        if len(script_item) > max_stackitem_size:
            raise ValueError(f'Stack item exceeds limit: len({script_item}) > {max_stackitem_size}')
        return OpPushString(script_item, script_item)
    elif isinstance(script_item, AssumeBool):
        return OpAssumeBool(script_item.top)
    else:
        raise ValueError(f'Unknown script item: {script_item}')


def parse_script(script: Sequence[ScriptItem], max_stackitem_size: int) -> Sequence[Op]:
    ops = []
    prev_item: int = None
    for script_item in script:
        if script_item == Opcode.OP_PICK or script_item == Opcode.OP_ROLL:
            if isinstance(prev_item, Opcode):
                prev_item = parse_int_op(prev_item)
            assert isinstance(prev_item, int)
            ops.pop()
            ops.append(OpPick(prev_item) if script_item == Opcode.OP_PICK else OpRoll(prev_item))
        elif script_item == Opcode.OP_CHECKMULTISIG or script_item == Opcode.OP_CHECKMULTISIGVERIFY:
            if isinstance(prev_item, Opcode):
                prev_item = parse_int_op(prev_item)
            assert isinstance(prev_item, int)
            ops.pop()
            ops.append(OpCheckMultiSig(prev_item, script_item, script_item == Opcode.OP_CHECKMULTISIGVERIFY))
        else:
            ops.append(parse_script_item(script_item, max_stackitem_size))
        prev_item = script_item
    return ops


def pretty_print_script(script: Sequence) -> str:
    strs = []
    for item in script:
        if isinstance(item, Opcode):
            strs.append(item.name)
        elif isinstance(item, (int, z3.BitVecNumRef)):
            strs.append(str(item))
        elif isinstance(item, (bool, z3.BoolRef)):
            item_str = str(item)
            if item_str == 'True':
                strs.append('OP_TRUE')
            else:
                strs.append('OP_FALSE')
        elif isinstance(item, str):
            if item.isprintable():
                strs.append(repr(item))
            else:
                strs.append(f'0x{item.encode().hex()}')
        elif isinstance(item, (bytes, z3.SeqRef)):
            if isinstance(item, z3.SeqRef):
                seq_str = item.as_string().replace("'", r"\'")
                item = literal_eval(f"b'{seq_str}'")
            try:
                s = item.decode()
            except:
                pass
            else:
                if s.isprintable():
                    strs.append(repr(s))
                    continue
            strs.append(f'0x{item.hex()}')
        elif isinstance(item, If):
            strs.append('OP_IF')
            strs.append(pretty_print_script(item.then))
            strs.append('OP_ELSE')
            strs.append(pretty_print_script(item.otherwise))
            strs.append('OP_ENDIF')
        elif isinstance(item, AssumeBool):
            strs.append(f'<OP_IF={item.top}>')
        else:
            strs.append(str(item))
    return ' '.join(strs)


def clean_nop(t: TransformedOps) -> TransformedOps:
    n_nops = 0
    for expected_input, output in zip(reversed(t.expected_inputs), t.outputs):
        if expected_input is not output:
            break
        n_nops += 1
    input_slice = slice(None) if not n_nops else slice(None, -n_nops)
    return TransformedOps(
        conditions=t.conditions,
        expected_inputs=t.expected_inputs[input_slice],
        expected_input_names=t.expected_input_names[input_slice],
        expected_input_sorts=t.expected_input_sorts[input_slice],
        outputs=t.outputs[n_nops:],
        output_sorts=t.output_sorts[n_nops:],
    )


def reconcile_inout(t1: TransformedOps, t2: TransformedOps) -> Tuple[TransformedOps, TransformedOps]:
    if len(t1.outputs) - len(t2.outputs) == len(t1.expected_inputs) - len(t2.expected_inputs):
        if len(t1.outputs) > len(t2.outputs):
            n = len(t1.outputs) - len(t2.outputs)
            return t1, TransformedOps(
                conditions=t2.conditions,
                expected_inputs=list(t1.expected_inputs[:n]) + list(t2.expected_inputs),
                expected_input_names=list(t1.expected_input_names[:n]) + list(t2.expected_input_names),
                expected_input_sorts=list(t1.expected_input_sorts[:n]) + list(t2.expected_input_sorts),
                outputs=list(t2.outputs) + list(t1.expected_inputs[-n:]),
                output_sorts=list(t2.output_sorts) + list(t1.expected_input_sorts[-n:]),
            )
        if len(t2.outputs) > len(t1.outputs):
            n = len(t2.outputs) - len(t1.outputs)
            return TransformedOps(
                conditions=t1.conditions,
                expected_inputs=list(t2.expected_inputs[:n]) + list(t1.expected_inputs),
                expected_input_names=list(t2.expected_input_names[:n]) + list(t1.expected_input_names),
                expected_input_sorts=list(t2.expected_input_sorts[:n]) + list(t1.expected_input_sorts),
                outputs=list(t1.outputs) + list(t2.expected_inputs[-n:]),
                output_sorts=list(t1.output_sorts) + list(t2.expected_input_sorts[-n:]),
            ), t2
    return t1, t2


def check_sorts(msg: str, sorts1: Sequence[Sort], sorts2: Sequence[Sort],
                opcodes1: Sequence[ScriptItem], opcodes2: Sequence[ScriptItem]):
    s = StringIO()
    if any(s1 != s2 and s1 != SortUnknown() and s2 != SortUnknown()
           for s1, s2 in zip(sorts1, sorts2)):
        print('Equivalence is FALSE.', msg, file=s)
        print('Left script:', file=s)
        print(end='A:     ', file=s)
        print(pretty_print_script(opcodes1), file=s)
        print('Right script:', file=s)
        print(end='B:     ', file=s)
        print(pretty_print_script(opcodes2), file=s)
        print(file=s)
        print('     |   Left   |   Right', file=s)
        print('----------------+-----------', file=s)
        for i, (s1, s2) in enumerate(zip(sorts1, sorts2)):
            if s1 != s2 and s1 != SortUnknown() and s2 != SortUnknown():
                print(end='=> ', file=s)
            else:
                print(end='   ', file=s)
            print('{} |{:^10}|{:^10}'.format(i, s1.to_c(), s2.to_c()), file=s)
        return s.getvalue()
    return None


def print_verify_state(s: TextIO, opcodes: Sequence[Op], statements: Statements, model: z3.ModelRef):
    verify_map = {
        idx: model.get_interp(var)
        for idx, var in zip(statements.verify_opcode_indices(), statements.verify_statements())
    }
    for idx, opcode in enumerate(opcodes):
        if idx in verify_map:
            print(end=f'<{pretty_print_script([opcode.opcode()])}={verify_map[idx]}> ', file=s)
        else:
            print(pretty_print_script([opcode.opcode()]), end=' ', file=s)
    print(file=s)


def prove_equivalence_single(opcodes1: Sequence[ScriptItem], opcodes2: Sequence[ScriptItem],
                             max_stackitem_size, verify=True, full_script: bool=False) -> Optional[str]:
    input_vars = VarNamesIdentity()
    funcs = FuncsDefault()
    statements1 = StatementsDefault(max_stackitem_size)
    statements2 = StatementsDefault(max_stackitem_size)

    ops1 = parse_script(opcodes1, max_stackitem_size)
    ops2 = parse_script(opcodes2, max_stackitem_size)

    t1 = transform_ops(ops1,
                       statements1, input_vars, VarNamesPrefix('a_', input_vars), funcs, full_script)
    t2 = transform_ops(ops2,
                       statements2, input_vars, VarNamesPrefix('b_', input_vars), funcs, full_script)

    if not full_script:
        t1 = clean_nop(t1)
        t2 = clean_nop(t2)
        t1, t2 = reconcile_inout(t1, t2)

    s = StringIO()

    assumptions = z3.And(
        *list(statements1.assumed_statements()) + list(statements2.assumed_statements()) + list(funcs.statements())
    )

    if full_script:
        if len(t1.outputs) == 0:  # enforce cleanstack
            solver = z3.Solver()
            claim = z3.Implies(assumptions, z3.Not(z3.And(*statements1.verify_statements())))
            solver.add(z3.Not(claim))
            unspendable1 = solver.check() == z3.unsat
        else:
            unspendable1 = True
        if len(t2.outputs) == 0:
            solver = z3.Solver()
            claim = z3.Implies(assumptions, z3.Not(z3.And(*statements2.verify_statements())))
            solver.add(z3.Not(claim))
            unspendable2 = solver.check() == z3.unsat
        else:
            unspendable2 = True
        if unspendable1 and unspendable2:
            return None

    if len(t1.outputs) != len(t2.outputs):
        print('Equivalence is FALSE. The two scripts produce a different number of outputs.', file=s)
        print('Left script:', file=s)
        print(end='A:     ', file=s)
        print(pretty_print_script(opcodes1), file=s)
        print('Right script:', file=s)
        print(end='B:     ', file=s)
        print(pretty_print_script(opcodes2), file=s)
        print(f'The left script produces {len(t1.outputs)} outputs, '
              f'while the right script produces {len(t2.outputs)}', file=s)
        return s.getvalue()
    if len(t1.expected_input_names) != len(t2.expected_input_names):
        print('Equivalence is FALSE. The two scripts take a different number of inputs.', file=s)
        print('Left script:', file=s)
        print(end='A:     ', file=s)
        print(pretty_print_script(opcodes1), file=s)
        print('Right script:', file=s)
        print(end='B:     ', file=s)
        print(pretty_print_script(opcodes2), file=s)
        print(f'The left script takes {len(t1.expected_input_names)} inputs, '
              f'while the right script takes {len(t2.expected_input_names)}', file=s)
        return s.getvalue()
    result_sorts = check_sorts('The two scripts take different datatypes as inputs.',
                               t1.expected_input_sorts, t2.expected_input_sorts, opcodes1, opcodes2)
    if result_sorts is not None:
        return result_sorts
    result_sorts = check_sorts('The two script produce different datatypes as outputs.',
                               t1.output_sorts, t2.output_sorts, opcodes1, opcodes2)
    if result_sorts is not None:
        return result_sorts

    problem = z3.And(*[a == b for a, b in zip(t1.outputs, t2.outputs)])
    if verify:
        problem = z3.And(
            problem,
            z3.And(*statements1.verify_statements()) == z3.And(*statements2.verify_statements()),
        )
    claim = z3.Implies(assumptions, problem)

    solver = z3.Solver()
    solver.add(z3.Not(claim))
    r = solver.check()
    if r == z3.unsat:
        return None
    needs_verbose = False
    if r == z3.unknown:
        print('Equivalence is UNKNOWN.', file=s)
        print('Z3 is unable to determine whether the scripts are equivalent.', file=s)
    else:
        print('Equivalence is FALSE, and CashProof can prove it mathematically.', file=s)
        print('Left script:', file=s)
        print(end='A:     ', file=s)
        print(pretty_print_script(opcodes1), file=s)
        print('Right script:', file=s)
        print(end='B:     ', file=s)
        print(pretty_print_script(opcodes2), file=s)
        print('CashProof found a COUNTEREXAMPLE:', file=s)
        print('Consider the following inputs:', file=s)
        print(end='I:     ', file=s)
        print(pretty_print_script([solver.model().get_interp(input_var) for input_var in t1.expected_inputs]), file=s)
        output1 = pretty_print_script([solver.model().get_interp(output_var) for output_var in t1.outputs])
        output2 = pretty_print_script([solver.model().get_interp(output_var) for output_var in t2.outputs])
        if output1 == output2:
            print('While the scripts produce the same output:', file=s)
        else:
            print('The two scripts produce different outputs:', file=s)
        print(end='A(I) = ', file=s)
        print(output1, file=s)
        print(end='B(I) = ', file=s)
        print(output2, file=s)

        if output1 == output2:
            print('Other invariants, such as OP_VERIFY differ.', file=s)
            print('Invariants can be introduced by OP_VERIFY, OP_EQUALVERIFY, OP_NUMEQUALVERIFY, OP_CHECKSIGVERIFY, \n'
                  'OP_CHECKMULTISIGVERIFY, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSEQUENCEVERIFY and OP_CHECKDATASIGVERIFY.',
                  file=s)
            print('Script A:', file=s)
            print_verify_state(s, ops1, statements1, solver.model())
            print('Script B:', file=s)
            print_verify_state(s, ops2, statements2, solver.model())
        if needs_verbose:
            print('-'*20, file=s)
            print('model:\n', solver.model(), file=s)
    if needs_verbose:
        print('-'*20, file=s)
        print('assumptions:\n', assumptions, file=s)
        print('-'*20, file=s)
        print('problem:\n', problem, file=s)
        print('-'*20, file=s)
        print('sorts:', file=s)
        for input_name, input_sort in zip(t1.expected_input_names, t1.expected_input_sorts):
            print(input_name, ' : ', input_sort, file=s)
    return s.getvalue()


def transform_ops(ops: Sequence[Op], statements: Statements, input_vars: VarNames, stack_vars: VarNames, funcs: Funcs,
                  full_script: bool):
    stack = StackStrict(input_vars)
    altstack = StackStrict(input_vars)
    stacks = Stacks(stack, altstack)
    op_var_names_list = []
    for op in ops:
        op_var_names_list.append(
            op.apply_stack(stacks, stack_vars)
        )
    sorts = stack.solve_all()
    vars_z3 = {}
    unknown = SortUnknown()
    for op_var_names in op_var_names_list:
        for var_name in list(op_var_names.inputs) + list(op_var_names.outputs):
            if var_name not in vars_z3:
                vars_z3[var_name] = z3.Const(var_name, sorts.get(var_name, unknown).to_z3())
    op_vars_list = []
    for op_var_names in op_var_names_list:
        op_vars_list.append(
            OpVars(
                [vars_z3[input_name] for input_name in op_var_names.inputs],
                [vars_z3[output_name] for output_name in op_var_names.outputs],
                op_var_names.data,
            )
        )
    for op, op_vars in zip(ops, op_vars_list):
        op.statements(statements, op_vars, stack_vars, funcs)
        statements.next_opcode()
    if full_script:
        if stacks.depth() == 0:
            raise ValueError('No final stack item on stack')
        statements.verify(z3.Const(stacks.pop(SortBool()), SortBool().to_z3()))

    return TransformedOps(
        conditions=[],
        expected_inputs=[vars_z3[var] for var in stack.input_var_names()],
        expected_input_names=stack.input_var_names(),
        expected_input_sorts=[sorts.get(var, unknown) for var in stack.input_var_names()],
        outputs=[vars_z3[var] for var in stack.output_var_names()],
        output_sorts=[sorts.get(var, unknown) for var in stack.output_var_names()],
    )
