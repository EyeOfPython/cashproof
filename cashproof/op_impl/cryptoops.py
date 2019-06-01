from typing import Sequence, Callable

import z3

from cashproof.func import Funcs
from cashproof.op import Op, OpVars, Ast, OpVarNames
from cashproof.opcodes import Opcode
from cashproof.sort import SortString, SortBool
from cashproof.stack import VarNames, Stacks
from cashproof.statements import Statements


def secp256k1_verify(var_names: VarNames, funcs: Funcs) -> Callable[..., Ast]:
    return funcs.define('SECP256k1_VERIFY', var_names, [SortString(), SortString(), SortString()], SortBool(), [])


def sha256(var_names: VarNames, funcs: Funcs) -> Callable[..., Ast]:
    return funcs.define('SHA256', var_names, [SortString()], SortString(), [])


class OpCheckSig(Op):
    def __init__(self, opcode: Opcode, verify: bool):
        self._opcode = opcode
        self._verify = verify

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        pubkey = stack.pop(SortString())
        sig = stack.pop(SortString())
        result = [] if self._verify else [stack.push(var_names.new(f'checksig({sig}, {pubkey})'), SortBool())]
        return OpVarNames([sig, pubkey], result)

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        sig, pubkey = op_vars.inputs
        verify_func = secp256k1_verify(var_names, funcs)
        preimage = z3.Const(var_names.glob('PREIMAGE'), SortString().to_z3())
        hash_func = sha256(var_names, funcs)
        data = hash_func(hash_func(preimage))
        if self._verify:
            statements.verify(verify_func(sig, data, pubkey))
        else:
            result, = op_vars.outputs
            statements.assume(result == verify_func(sig, data, pubkey))


class OpCheckMultiSig(Op):
    def __init__(self, num_sigs: int, opcode: Opcode, verify: bool):
        self._num_sigs = num_sigs
        self._opcode = opcode
        self._verify = verify

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        publickeys = [stack.pop(SortString()) for _ in range(self._num_sigs)]
        signatures = [stack.pop(SortString()) for _ in range(self._num_sigs)]
        dummy = stack.pop(SortString())
        results = [] if \
            self._verify else \
            [stack.push(var_names.new(f'checkmultisig({signatures}, {publickeys})'), SortBool())]
        return OpVarNames([dummy] + list(reversed(signatures)) + list(reversed(publickeys)), results)

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        _, *inputs = op_vars.inputs
        signatures = inputs[:len(inputs) // 2]
        publickeys = inputs[len(inputs) // 2:]
        preimage = z3.Const(var_names.glob('PREIMAGE'), SortString().to_z3())
        verify_func = secp256k1_verify(var_names, funcs)
        hash_func = sha256(var_names, funcs)
        data = hash_func(hash_func(preimage))
        if self._verify:
            for sig, pubkey in zip(signatures, publickeys):
                statements.verify(verify_func(sig, data, pubkey))
        else:
            result, = op_vars.outputs
            statements.assume(
                z3.And(*[result == verify_func(sig, data, pubkey)
                         for sig, pubkey in zip(signatures, publickeys)])
            )


class OpCheckDataSig(Op):
    def __init__(self, opcode: Opcode, verify: bool):
        self._opcode = opcode
        self._verify = verify

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        pubkey = stack.pop(SortString())
        msg = stack.pop(SortString())
        sig = stack.pop(SortString())
        results = [] if \
            self._verify else \
            [stack.push(var_names.new(f'checkdatasig({sig}, {msg}, {pubkey})'), SortBool())]
        return OpVarNames([sig, msg, pubkey], results)

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        sig, msg, pubkey = op_vars.inputs
        func = secp256k1_verify(var_names, funcs)
        data = sha256(var_names, funcs)(msg)
        if self._verify:
            statements.verify(func(sig, data, pubkey))
        else:
            result, = op_vars.outputs
            statements.assume(result == func(sig, data, pubkey))


class OpHash(Op):
    def __init__(self, opcode: Opcode, hash_funcs: Sequence[str]):
        self._opcode = opcode
        self._hash_funcs = hash_funcs

    def opcode(self) -> Opcode:
        return self._opcode

    def apply_stack(self, stack: Stacks, var_names: VarNames) -> OpVarNames:
        data = stack.pop(SortString())
        name = '.'.join(self._hash_funcs)
        return OpVarNames([data], [stack.push(f'{name}({data})', SortString())])

    def statements(self, statements: Statements, op_vars: OpVars, var_names: VarNames, funcs: Funcs) -> None:
        data, = op_vars.inputs
        hashed, = op_vars.outputs
        for hash_func in reversed(self._hash_funcs):
            func = funcs.define(hash_func, var_names, [SortString()], SortString(), [])
            data = func(data)
        statements.assume(data == hashed)


CRYPTO_OPS = [
    OpHash(Opcode.OP_RIPEMD160, ['RIPEMD160']),
    OpHash(Opcode.OP_SHA1,      ['SHA1']),
    OpHash(Opcode.OP_SHA256,    ['SHA256']),
    OpHash(Opcode.OP_HASH160,   ['RIPEMD160', 'SHA256']),
    OpHash(Opcode.OP_HASH256,   ['SHA256', 'SHA256']),

    OpCheckSig(Opcode.OP_CHECKSIG, False),
    OpCheckSig(Opcode.OP_CHECKSIGVERIFY, True),
    OpCheckDataSig(Opcode.OP_CHECKDATASIG, False),
    OpCheckDataSig(Opcode.OP_CHECKDATASIGVERIFY, True),
]
