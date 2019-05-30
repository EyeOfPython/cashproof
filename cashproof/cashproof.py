from dataclasses import dataclass
from typing import Union, List, Dict, Set

import z3

from cashproof.opcodes import Opcode


@dataclass
class If:
    then: List['Op']
    otherwise: List['Op']


@dataclass
class NotIf:
    then: List['Op']
    otherwise: List['Op']


@dataclass
class Pick:
    depth: int


@dataclass
class Roll:
    depth: int


Op = Union[Opcode, bytes, int, If, NotIf, Pick, Roll]


class Stack:
    def __init__(self, prefix: str = '') -> None:
        self._prefix = prefix
        self._var_counter = 0
        self._stack_vars: List[z3.Ast] = []

    def pop(self) -> z3.Ast:
        return self._stack_vars.pop()

    def push(self, var: z3.Ast) -> None:
        self._stack_vars.append(var)

    def push_new(self, typ=z3.Int) -> z3.Ast:
        var_name = f'{self._prefix}var{self._var_counter}'
        self._var_counter += 1
        var = typ(var_name)
        self._stack_vars.append(var)
        return var

    def nth_back(self, n: int) -> z3.Ast:
        n += 1
        return self._stack_vars[-n]

    def pop_nth_back(self, n: int) -> z3.Ast:
        n += 1
        return self._stack_vars.pop(-n)

    def list(self) -> List[z3.Ast]:
        return list(self._stack_vars)


class Funcs:
    def __init__(self) -> None:
        self._funcs: Dict[str, z3.Function] = {}
        self._statements = []

    @staticmethod
    def get_func_var(func_name: str, var_name: str) -> z3.Ast:
        return z3.Int(f'{func_name}{var_name}')

    def get_func(self, name: str, n_args: int, properties: Set[str], result_type=z3.IntSort, input_type=z3.IntSort) \
                -> z3.Function:
        if name in self._funcs:
            return self._funcs[name]
        func = z3.Function(name, *[input_type()] * n_args + [result_type()])
        self._funcs[name] = func
        if 'associative' in properties:
            a = self.get_func_var(name, 'a')
            b = self.get_func_var(name, 'b')
            c = self.get_func_var(name, 'c')
            self._statements.append(z3.ForAll((a, b, c), func(func(a, b), c) == func(a, func(b, c))))
        if 'commutative':
            x = self.get_func_var(name, 'x')
            y = self.get_func_var(name, 'y')
            self._statements.append(z3.ForAll((x, y), func(x, y) == func(y, x)))
        return func

    def statements(self) -> List[z3.Ast]:
        return list(self._statements)


class BuildAst:
    def __init__(self, prefix: str, input_vars: List[str], funcs: Funcs) -> None:
        self._consts: Dict[Union[int, bytes], z3.Ast] = {}
        self._funcs = funcs
        self._statements: List[Union[bool, z3.Ast]] = []
        self._prefix = prefix
        self._alt_stack = Stack(f'{prefix}alt')
        self._stack = Stack(prefix)
        for var in input_vars:
            self._stack.push(z3.Int(var))

    def get_const(self, value: Union[int, bytes]) -> z3.Ast:
        if isinstance(value, int):
            return value
        return int.from_bytes(value, byteorder='little')

    def _binop(self, *names: str, properties: Set[str]):
        first = self._stack.pop()
        second = self._stack.pop()
        for name in names:
            result = self._stack.push_new()
            self._statements.append(result == self._funcs.get_func(name, 2, properties)(first, second))

    def _unary_op(self, name: str):
        top = self._stack.pop()
        result = self._stack.push_new()
        self._statements.append(result == self._funcs.get_func(name, 1, set())(top))

    def _verify(self, stmt: Union[z3.Ast, bool]=None):
        if stmt is None:
            stmt = self._stack.pop() != 0
        self._statements.append(self._funcs.get_func('verify', 1, set(), z3.BoolSort, z3.BoolSort)(stmt))

    def add_op(self, op: Op) -> None:
        if isinstance(op, Opcode):
            if op == Opcode.OP_0:
                self._stack.push(self.get_const(0))
            elif op == Opcode.OP_1NEGATE:
                self._stack.push(self.get_const(-1))
            elif Opcode.OP_1.value <= op.value <= Opcode.OP_16.value:
                self._stack.push(self.get_const(op.value - Opcode.OP_1.value + 1))
            elif op == Opcode.OP_VERIFY:
                raise NotImplemented
            elif op == Opcode.OP_RETURN:
                raise NotImplemented
            elif op == Opcode.OP_TOALTSTACK:
                self._alt_stack.push(self._stack.pop())
            elif op == Opcode.OP_FROMALTSTACK:
                self._stack.push(self._alt_stack.pop())
            elif op == Opcode.OP_IFDUP:
                raise NotImplemented
            elif op == Opcode.OP_DEPTH:
                self._stack.push_new()
            elif op == Opcode.OP_DROP:
                self._stack.pop()
            elif op == Opcode.OP_DUP:
                top = self._stack.pop()
                self._stack.push(top)
                self._stack.push(top)
            elif op == Opcode.OP_NIP:
                top = self._stack.pop()
                self._stack.pop()
                self._stack.push(top)
            elif op == Opcode.OP_OVER:
                first = self._stack.pop()
                second = self._stack.pop()
                self._stack.push(second)
                self._stack.push(first)
                self._stack.push(second)
            elif op == Opcode.OP_ROT:
                first = self._stack.pop()
                second = self._stack.pop()
                third = self._stack.pop()
                self._stack.push(second)
                self._stack.push(first)
                self._stack.push(third)
            elif op == Opcode.OP_SWAP:
                first = self._stack.pop()
                second = self._stack.pop()
                self._stack.push(first)
                self._stack.push(second)
            elif op == Opcode.OP_TUCK:
                first = self._stack.pop()
                second = self._stack.pop()
                self._stack.push(second)
                self._stack.push(first)
                self._stack.push(second)
            elif op == Opcode.OP_2DROP:
                self._stack.pop()
                self._stack.pop()
            elif op == Opcode.OP_2DUP:
                top = self._stack.pop()
                self._stack.push(top)
                self._stack.push(top)
                self._stack.push(top)
            elif op == Opcode.OP_3DUP:
                top = self._stack.pop()
                self._stack.push(top)
                self._stack.push(top)
                self._stack.push(top)
                self._stack.push(top)
            elif op == Opcode.OP_2OVER:
                first = self._stack.pop()
                second = self._stack.pop()
                third = self._stack.pop()
                fourth = self._stack.pop()
                self._stack.push(fourth)
                self._stack.push(third)
                self._stack.push(second)
                self._stack.push(first)
                self._stack.push(fourth)
                self._stack.push(third)
            elif op == Opcode.OP_2ROT:
                raise NotImplemented
            elif op == Opcode.OP_2SWAP:
                first = self._stack.pop()
                second = self._stack.pop()
                third = self._stack.pop()
                fourth = self._stack.pop()
                self._stack.push(second)
                self._stack.push(first)
                self._stack.push(fourth)
                self._stack.push(third)
            elif op == Opcode.OP_CAT:
                self._binop('cat', properties={'associative'})
            elif op == Opcode.OP_SPLIT:
                self._binop('split_left', 'split_right', properties=set())
            elif op == Opcode.OP_NUM2BIN:
                self._binop('num2bin', properties=set())
            elif op == Opcode.OP_BIN2NUM:
                self._unary_op('bin2num')
            elif op == Opcode.OP_SIZE:
                top = self._stack.pop()
                size = self._stack.push_new()
                self._statements.append(size == self._funcs.get_func('size', 1, set())(top))
            elif op == Opcode.OP_INVERT:
                raise NotImplemented
            elif op == Opcode.OP_AND:
                self._binop('bit_and', properties={'associative', 'commutative'})
            elif op == Opcode.OP_OR:
                self._binop('bit_or', properties={'associative', 'commutative'})
            elif op == Opcode.OP_XOR:
                self._binop('bit_xor', properties={'associative', 'commutative'})
            elif op == Opcode.OP_EQUAL or op == Opcode.OP_NUMEQUAL:
                first = self._stack.pop()
                second = self._stack.pop()
                equal = self._stack.push_new(z3.Bool)
                self._statements.append(equal == (first == second))
            elif op == Opcode.OP_EQUALVERIFY or op == Opcode.OP_NUMEQUALVERIFY:
                first = self._stack.pop()
                second = self._stack.pop()
                self._verify(first == second)
            elif op == Opcode.OP_1ADD:
                top = self._stack.pop()
                add1 = self._stack.push_new()
                self._statements.append(add1 == top + 1)
            elif op == Opcode.OP_1SUB:
                top = self._stack.pop()
                sub1 = self._stack.push_new()
                self._statements.append(sub1 == top - 1)
            elif op == Opcode.OP_2MUL:
                raise NotImplemented
            elif op == Opcode.OP_2DIV:
                raise NotImplemented
            elif op == Opcode.OP_NEGATE:
                top = self._stack.pop()
                neg = self._stack.push_new()
                self._statements.append(neg == -top)
            elif op == Opcode.OP_ABS:
                top = self._stack.pop()
                abs_val = self._stack.push_new()
                self._statements.append(z3.If(top > 0, top == abs_val, top == -abs_val))
            elif op == Opcode.OP_NOT:
                top = self._stack.pop()
                not_val = self._stack.push_new(z3.Bool)
                if isinstance(top, z3.Bool):
                    self._statements.append(not_val == z3.Not(top))
                else:
                    self._statements.append(z3.If(top == 0, not_val == 1, not_val == 0))
            elif op == Opcode.OP_0NOTEQUAL:
                top = self._stack.pop()
                not_val = self._stack.push_new(z3.Bool)
                self._statements.append(not_val == (top != 0))
            elif op == Opcode.OP_ADD:
                first = self._stack.pop()
                second = self._stack.pop()
                add = self._stack.push_new()
                self._statements.append(add == first + second)
            elif op == Opcode.OP_SUB:
                first = self._stack.pop()
                second = self._stack.pop()
                sub = self._stack.push_new()
                self._statements.append(sub == first - second)
            elif op == Opcode.OP_MUL:
                raise NotImplemented
            elif op == Opcode.OP_DIV:
                first = self._stack.pop()
                second = self._stack.pop()
                mul = self._stack.push_new()
                self._statements.append(mul == first * second)
            elif op == Opcode.OP_MOD:
                first = self._stack.pop()
                second = self._stack.pop()
                mod = self._stack.push_new()
                self._statements.append(mod == first % second)
            elif op == Opcode.OP_LSHIFT:
                raise NotImplemented
            elif op == Opcode.OP_RSHIFT:
                raise NotImplemented
            elif op == Opcode.OP_BOOLAND:
                first = self._stack.pop()
                second = self._stack.pop()
                and_val = self._stack.push_new(z3.Bool)
                self._statements.append(and_val == z3.And(first, second))
            elif op == Opcode.OP_BOOLOR:
                first = self._stack.pop()
                second = self._stack.pop()
                or_val = self._stack.push_new(z3.Bool)
                self._statements.append(or_val == z3.Or(first, second))
            elif op == Opcode.OP_NUMNOTEQUAL:
                first = self._stack.pop()
                second = self._stack.pop()
                not_equal = self._stack.push_new(z3.Bool)
                self._statements.append(not_equal == (first != second))
            elif op == Opcode.OP_LESSTHAN:
                first = self._stack.pop()
                second = self._stack.pop()
                lt = self._stack.push_new(z3.Bool)
                self._statements.append(lt == (second < first))
            elif op == Opcode.OP_GREATERTHAN:
                first = self._stack.pop()
                second = self._stack.pop()
                lt = self._stack.push_new(z3.Bool)
                self._statements.append(lt == (second > first))
            elif op == Opcode.OP_LESSTHANOREQUAL:
                first = self._stack.pop()
                second = self._stack.pop()
                lt = self._stack.push_new(z3.Bool)
                self._statements.append(lt == (second <= first))
            elif op == Opcode.OP_GREATERTHANOREQUAL:
                first = self._stack.pop()
                second = self._stack.pop()
                lt = self._stack.push_new(z3.Bool)
                self._statements.append(lt == (second >= first))
            elif op == Opcode.OP_MIN:
                first = self._stack.pop()
                second = self._stack.pop()
                min_val = self._stack.push_new()
                self._statements.append(z3.If(first > second, min_val == second, min_val == first))
            elif op == Opcode.OP_MAX:
                first = self._stack.pop()
                second = self._stack.pop()
                max_val = self._stack.push_new()
                self._statements.append(z3.If(first > second, max_val == first, max_val == second))
            elif op == Opcode.OP_WITHIN:
                value = self._stack.pop()
                min_bound = self._stack.pop()
                max_bound = self._stack.pop()
                within = self._stack.push_new(z3.Bool)
                self._statements.append(within == z3.And(value >= min_bound, value < max_bound))
            elif op == Opcode.OP_RIPEMD160:
                self._unary_op('ripemd160')
            elif op == Opcode.OP_SHA1:
                self._unary_op('sha1')
            elif op == Opcode.OP_SHA256:
                self._unary_op('sha256')
            elif op == Opcode.OP_HASH160:
                self._unary_op('hash160')
            elif op == Opcode.OP_HASH256:
                self._unary_op('hash256')
            elif op == Opcode.OP_CODESEPARATOR:
                pass
            elif op == Opcode.OP_CHECKSIG:
                pk = self._stack.pop()
                sig = self._stack.pop()
                sig_valid = self._stack.push_new()
                self._statements.append(sig_valid == self._funcs.get_func('checksig', 2, set(), z3.BoolSort)(pk, sig))
            elif op == Opcode.OP_CHECKSIGVERIFY:
                raise NotImplemented
            elif op == Opcode.OP_CHECKMULTISIG:
                raise NotImplemented
            elif op == Opcode.OP_CHECKMULTISIGVERIFY:
                raise NotImplemented
        elif isinstance(op, Pick):
            self._stack.push(self._stack.nth_back(op.depth))
        elif isinstance(op, Roll):
            self._stack.push(self._stack.pop_nth_back(op.depth))

    def prove_equivalence(self, other: 'BuildAst'):
        if len(self._stack.list()) != len(other._stack.list()):
            print('stacks have unequal size')
        stack_equal = z3.And(*[a == b for a, b in zip(self._stack.list(), other._stack.list())])
        a = z3.And(*self._statements)
        b = z3.And(*other._statements)
        f = z3.And(*self._funcs.statements())
        print(stack_equal)
        print(a)
        print(b)
        print(f)
        z3.prove(z3.Implies(z3.And(a, b, f), stack_equal))
