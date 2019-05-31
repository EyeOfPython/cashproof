from dataclasses import dataclass
from typing import Sequence, Union, Iterable, List, Tuple

import z3

from cashproof.func import Funcs, FuncsDefault
from cashproof.op import Op, OpVars, OpVarNames, Ast
from cashproof.op_impl.bitlogicops import BIT_LOGIC_OPS
from cashproof.op_impl.controlops import CONTROL_OPS
from cashproof.op_impl.cryptoops import CRYPTO_OPS
from cashproof.op_impl.numericops import NUMERIC_OPS
from cashproof.op_impl.pushops import OpPushInt, OpPushString, OpPushBool
from cashproof.op_impl.spliceops import SPLICE_OPS
from cashproof.op_impl.stackops import STACK_OPS
from cashproof.opcodes import Opcode
from cashproof.sort import Sort, SortUnknown, SortBool
from cashproof.stack import Stacks, StackStrict, VarNamesIdentity, VarNames, VarNamesPrefix
from cashproof.statements import StatementsDefault, Statements

OPS = {
    op.opcode(): op
    for op in STACK_OPS + SPLICE_OPS + CONTROL_OPS + BIT_LOGIC_OPS + NUMERIC_OPS + CRYPTO_OPS
}


ScriptItem = Union[Opcode, int, str, bytes, bool, 'If']


@dataclass
class If:
    # inverted: bool
    then: Sequence[ScriptItem]
    otherwise: Sequence[ScriptItem]


@dataclass
class TransformedOps:
    conditions: Sequence[Tuple[str, bool]]
    expected_inputs: Sequence[z3.Ast]
    expected_input_names: Sequence[str]
    expected_input_sorts: Sequence[Sort]
    outputs: Sequence[z3.Ast]


def parse_script_item(script_item: ScriptItem) -> Op:
    if isinstance(script_item, Opcode):
        return OPS[script_item]
    elif isinstance(script_item, bool):
        return OpPushBool(..., script_item)
    elif isinstance(script_item, int):
        return OpPushInt(..., script_item)
    elif isinstance(script_item, (str, bytes)):
        return OpPushString(..., script_item)
    else:
        raise ValueError(f'Unknown script item: {script_item}')


# def conditional_outputs(transformed_ops: List[TransformedOps]):
#     def to_ast(cond_dict):
#         stmts = []
#         stmt = cond_dict.pop('expect', None)
#         if stmt is not None:
#             return stmt
#         for cond_var_name, next_cond_dict in cond_dict.items():
#             cond_var = z3.Bool(cond_var_name)
#             stmts.append(z3.If(cond_var, to_ast(next_cond_dict['then']), to_ast(next_cond_dict['otherwise'])))
#         return z3.And(*stmts)
#
#     outputs = {}
#     for t in transformed_ops:
#         for i, output in enumerate(t.outputs):
#             cond = outputs.setdefault(i, {})
#             for var_name, holds in t.conditions:
#                 cond = cond.setdefault(var_name, {}).setdefault('then' if holds else 'otherwise', {})
#             cond['expect'] = output
#     output_conds = {
#         i: to_ast(cond_dict)
#         for i, cond_dict in outputs.items()
#     }
#
#     print(output_conds)


def prove_equivalence(opcodes1: Sequence[ScriptItem], opcodes2: Sequence[ScriptItem], verify=True):
    input_vars = VarNamesIdentity()
    funcs = FuncsDefault()
    statements1 = StatementsDefault()
    statements2 = StatementsDefault()

    t1 = transform_ops([parse_script_item(op) for op in opcodes1],
                       statements1, input_vars, VarNamesPrefix('a_', input_vars), funcs)
    t2 = transform_ops([parse_script_item(op) for op in opcodes2],
                       statements2, input_vars, VarNamesPrefix('b_', input_vars), funcs)

    assumptions = z3.And(
        *list(statements1.assumed_statements()) + list(statements2.assumed_statements()) + list(funcs.statements())
    )
    problem = z3.And(*[a == b for a, b in zip(t1.outputs, t2.outputs)])
    if verify:
        verify_problem = z3.And(*[a == b for a, b in zip(statements1.verify_statements(),
                                                         statements2.verify_statements())])
        problem = z3.And(problem, verify_problem)
    z3.prove(z3.Implies(assumptions, problem))

    print('-----------'*4)
    print('assuming', assumptions)
    print('holds', problem)
    for input_name, input_sort in zip(t1.expected_input_names, t1.expected_input_sorts):
        print(input_name, ':', input_sort)


# def recurse_script(script_items: Sequence[ScriptItem],
#                    ops: Sequence[Op],
#                    op_var_names: Sequence[OpVarNames],
#                    condition_stack: List[Tuple[str, bool]],
#                    stack: Stacks,
#                    var_names: VarNames,
#                    statements: Statements,
#                    funcs: Funcs):
#     new_ops = list(ops)
#     new_op_var_names = list(op_var_names)
#     for script_item in script_items:
#         if isinstance(script_item, If):
#             condition_var = stack.pop(SortBool())
#             condition = z3.Const(condition_var, SortBool().to_z3())
#             stack_copy = stack.copy()
#             new_op_var_names.append(OpVarNames([condition_var], []))
#             new_ops.append(None)
#
#             statements.begin_if(condition)
#             yield from recurse_script(
#                 script_items=script_item.then,
#                 ops=new_ops,
#                 op_var_names=new_op_var_names,
#                 condition_stack=condition_stack + [(condition_var, True)],
#                 stack=stack,
#                 var_names=VarNamesPrefix(f'{condition_var}_true_', var_names),
#                 statements=statements,
#                 funcs=funcs,
#             )
#             statements.begin_else()
#             yield from recurse_script(
#                 script_items=script_item.otherwise,
#                 ops=new_ops,
#                 op_var_names=new_op_var_names,
#                 condition_stack=condition_stack + [(condition_var, False)],
#                 stack=stack_copy,
#                 var_names=VarNamesPrefix(f'{condition_var}_false_', var_names),
#                 statements=statements,
#                 funcs=funcs,
#             )
#             statements.end_if()
#         else:
#             op = parse_script_item(script_item)
#             new_ops.append(op)
#             op_var_names_instance = op.apply_stack(stack, var_names)
#             new_op_var_names.append(op_var_names_instance)
#     sorts = stack.solve_all()
#     print(sorts, new_op_var_names)
#     vars_z3 = {}
#     unknown = SortUnknown()
#     for op_var_names in new_op_var_names:
#         for var_name in list(op_var_names.inputs) + list(op_var_names.outputs):
#             if var_name not in vars_z3:
#                 vars_z3[var_name] = z3.Const(var_name, sorts.get(var_name, unknown).to_z3())
#     op_vars_list = []
#     for op_var_names in new_op_var_names:
#         op_vars_list.append(
#             OpVars(
#                 [vars_z3[input_name] for input_name in op_var_names.inputs],
#                 [vars_z3[output_name] for output_name in op_var_names.outputs],
#             )
#         )
#     for op, op_vars in zip(new_ops, op_vars_list):
#         if op is None:
#             continue
#         op.statements(statements, op_vars, var_names, funcs)
#
#     yield TransformedOps(
#         conditions=condition_stack,
#         expected_inputs=[vars_z3[var] for var in stack.input_var_names()],
#         expected_input_names=stack.input_var_names(),
#         expected_input_sorts=[sorts[var] for var in stack.input_var_names()],
#         outputs=[vars_z3[var] for var in stack.output_var_names()],
#     )


def transform_ops(ops: Sequence[Op], statements: Statements, input_vars: VarNames, stack_vars: VarNames, funcs: Funcs):
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
            )
        )
    for op, op_vars in zip(ops, op_vars_list):
        op.statements(statements, op_vars, stack_vars, funcs)

    return TransformedOps(
        conditions=[],
        expected_inputs=[vars_z3[var] for var in stack.input_var_names()],
        expected_input_names=stack.input_var_names(),
        expected_input_sorts=[sorts[var] for var in stack.input_var_names()],
        outputs=[vars_z3[var] for var in stack.output_var_names()],
    )
