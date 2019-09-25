from dataclasses import dataclass
from itertools import zip_longest
from typing import List, Sequence, Optional
from io import StringIO

from cashproof.ops import ScriptItem, If, AssumeBool, prove_equivalence_single


@dataclass
class Case:
    bools: List[bool]
    ops: List[ScriptItem]


def split_cases(ops: Sequence[ScriptItem], cases: List[Case]):
    def add_items(current_cases, items, bools):
        new_cases = []
        for current_case in current_cases:
            new_cases.append(Case(current_case.bools + bools, current_case.ops + items))
        return new_cases
    for op in ops:
        if isinstance(op, If):
            then = split_cases(op.then, add_items(cases, [AssumeBool(True)], [True]))
            otherwise = split_cases(op.otherwise, add_items(cases, [AssumeBool(False)], [False]))
            cases = then + otherwise
        else:
            cases = add_items(cases, [op], [])
    return cases


def prove_equivalence_cases(opcodes1: Sequence[ScriptItem], opcodes2: Sequence[ScriptItem],
                            max_stackitem_size, full_script: bool) -> Optional[str]:
    cases1 = split_cases(opcodes1, [Case([], [])])
    cases2 = split_cases(opcodes2, [Case([], [])])
    s = StringIO()
    for i, (case1, case2) in enumerate(zip_longest(cases1, cases2)):
        if case1 is None or case2 is None or case1.bools != case2.bools:
            print('Equivalence is FALSE, OP_IF blocks don\'t match.', file=s)
            print('CashScript requires the outlining structure of OP_IF blocks to match.', file=s)
            print(f'However, the structure differs at OP_IF case number {i}.', file=s)
            if case1 is None or not case1.bools:
                print(f'The left side has no OP_IF case, while the right side does.', file=s)
            elif case2 is None or not case2.bools:
                print(f'The right side has no OP_IF case, while the left side does.', file=s)
            else:
                print(f'The two sides have a matching OP_IF, but the nesting differs.', file=s)
                print(f'The left side takes bools {case1.bools}, while the right side takes bools {case2.bools}.',
                      file=s)
            return s.getvalue()
    for case1, case2 in zip(cases1, cases2):
        result = prove_equivalence_single(case1.ops, case2.ops, max_stackitem_size, full_script=full_script)
        if result is not None:
            return result
    return None
