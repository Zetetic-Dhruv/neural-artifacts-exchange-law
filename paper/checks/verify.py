#!/usr/bin/env python3
"""Reproducible finite checks for Model Inference from Neural Artifacts.

The integer checks are exact. Softmax checks use NumPy float64. These are
computational checks of constructions, not training or generalization experiments.
Run: python checks/verify.py
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
import itertools
import json
import math
import platform
import numpy as np
from literal_checks import check_literal_forests
from monoid_checks import check_monoids, check_symbol_hardening, check_coupled_min
from algebra_checks import (check_read_quotients, check_chain_exchange,
                           check_boolean_exchange, direct_equivalence)


def minimize(table: np.ndarray, outputs: np.ndarray, init: int):
    """Moore refinement, restricted to states reachable from init."""
    reached = {init}
    todo = [init]
    while todo:
        u = todo.pop()
        for v in table[u]:
            v = int(v)
            if v not in reached:
                reached.add(v)
                todo.append(v)
    states = sorted(reached)
    def number(signatures):
        classes = {}
        ans = {}
        for u, sig in signatures:
            ans[u] = classes.setdefault(sig, len(classes))
        return ans
    part = number((u, int(outputs[u])) for u in states)
    while True:
        nxt = number((u, (int(outputs[u]), *(part[int(v)] for v in table[u])))
                     for u in states)
        if nxt == part:
            return part
        part = nxt


@dataclass
class FFNMachine:
    w1: np.ndarray
    b1: np.ndarray
    w2: np.ndarray
    readout: np.ndarray
    init: int
    n: int
    m: int


def compile_machine(table: np.ndarray, output: np.ndarray, init: int) -> FFNMachine:
    n, m = table.shape
    w1 = np.zeros((n*m, n+m), dtype=np.int64)
    w2 = np.zeros((n, n*m), dtype=np.int64)
    for i, j in itertools.product(range(n), range(m)):
        h = i*m+j
        w1[h, i] = w1[h, n+j] = 1
        w2[int(table[i, j]), h] = 1
    readout = np.zeros((int(output.max())+1, n), dtype=np.int64)
    readout[output, np.arange(n)] = 1
    return FFNMachine(w1, -np.ones(n*m, dtype=np.int64), w2,
                      readout, init, n, m)


def extract_machine(net: FFNMachine):
    """Read only operational weights and the declared one-hot interface."""
    table = np.zeros((net.n, net.m), dtype=np.int64)
    # A single integer batched matrix evaluation checks the whole interface.
    x = np.zeros((net.n*net.m, net.n+net.m), dtype=np.int64)
    for i, j in itertools.product(range(net.n), range(net.m)):
        x[i*net.m+j, i] = x[i*net.m+j, net.n+j] = 1
    y = np.maximum(x @ net.w1.T + net.b1, 0) @ net.w2.T
    if not np.all((y == 0) | (y == 1)) or not np.all(y.sum(axis=1) == 1):
        raise ValueError('The transition does not close on the one-hot interface.')
    table[:] = np.argmax(y, axis=1).reshape(net.n, net.m)
    if not np.all(net.readout.sum(axis=0) == 1):
        raise ValueError('Invalid finite readout.')
    output = np.argmax(net.readout, axis=0)
    return table, output, minimize(table, output, net.init)


def check_machine_extraction():
    rng = np.random.default_rng(20260907)
    machines = transitions = 0
    for k in range(1, 4):
        top = (1 << k)-1
        for bits in range(1 << top):
            elems = [u for u in range(top) if bits >> u & 1] + [top]
            member = set(elems)
            if not all(u & v in member for u in elems for v in elems):
                continue
            idx = {u:i for i,u in enumerate(elems)}
            table = np.array([[idx[u & v] for v in elems] for u in elems])
            outputs = list(itertools.product((0, 1), repeat=len(elems)))
            outputs += [tuple(next((j for j in range(k) if u >> j & 1), k)
                              for u in elems)]
            for out in outputs:
                out = np.array(out, dtype=np.int64)
                net = compile_machine(table, out, idx[top])
                # A hidden-neuron permutation changes weights but not the machine.
                perm = rng.permutation(net.n*net.m)
                net.w1, net.b1, net.w2 = net.w1[perm], net.b1[perm], net.w2[:,perm]
                t, o, part = extract_machine(net)
                assert np.array_equal(t, table) and np.array_equal(o, out)
                relation = direct_equivalence(elems, dict(zip(elems, map(int,out))))
                assert all((part[i] == part[j]) == ((u,v) in relation)
                           for i,u in enumerate(elems) for j,v in enumerate(elems))
                machines += 1
                transitions += table.size
    return {'machines': machines, 'exact_transition_checks': transitions,
            'hidden_permutation_seed': 20260907, 'all_quotients_match': True}


@dataclass(frozen=True)
class Code:
    base: int | None = None
    threshold: float | None = None
    children: tuple | None = None
    flip: int = 0


@dataclass
class Network:
    keys: np.ndarray | None
    children: tuple | None
    w1: np.ndarray
    b1: np.ndarray
    w2: np.ndarray


BASE = np.array([[0]*8, [1]*8, [x % 2 for x in range(8)],
                 [1-x % 2 for x in range(8)]], dtype=np.int64)


def eval_code(code: Code, x: int) -> int:
    if code.base is not None:
        return int(BASE[code.base, x])
    child = int(x > code.threshold)
    return eval_code(code.children[child], x) ^ code.flip


def compile_code(code: Code) -> Network:
    if code.base is not None:
        w2 = np.eye(2)[BASE[code.base]].T
        return Network(None, None, np.eye(8), np.zeros(8), w2)
    t = code.threshold
    keys = np.array([[t, -1], [-t, 1]], dtype=float)
    # Finite-symbol cleanup followed by the chosen identity/flip table.
    h = np.eye(2)[:, [code.flip, 1 ^ code.flip]]
    w1 = np.vstack([np.eye(2), np.eye(2)])
    b1 = np.array([-.25, -.25, -.75, -.75])
    w2 = np.hstack([2*h, -2*h])
    return Network(keys, tuple(compile_code(c) for c in code.children), w1,b1,w2)


def ffn(net: Network, x: np.ndarray) -> np.ndarray:
    return net.w2 @ np.maximum(net.w1 @ x + net.b1, 0)


def eval_network(net: Network, x: int, temperature: float = 0) -> np.ndarray:
    if net.keys is None:
        return ffn(net, np.eye(8)[x])
    scores = net.keys @ np.array([1, x])
    vals = np.array([eval_network(c,x,temperature) for c in net.children])
    if temperature == 0:
        v = vals[int(np.argmax(scores))]
    else:
        p = np.exp((scores-scores.max())/temperature)
        p /= p.sum()
        v = p @ vals
    return ffn(net,v)


def extract_code(net: Network):
    """Extract affine scores, finite maps, and wiring, without source-code tags."""
    if net.keys is None:
        table = tuple(int(np.argmax(ffn(net,np.eye(8)[x]))) for x in range(8))
        return {'table':table}
    table = tuple(int(np.argmax(ffn(net,np.eye(2)[y]))) for y in range(2))
    return {'scores':net.keys.tolist(), 'map':table,
            'children':tuple(extract_code(c) for c in net.children)}


def eval_extracted(c, x):
    if 'table' in c:
        return c['table'][x]
    scores = [v[0]+v[1]*x for v in c['scores']]
    i = max(range(len(scores)), key=lambda j:scores[j])
    return c['map'][eval_extracted(c['children'][i],x)]


def codes():
    for b in range(4):
        yield Code(base=b)
    for t, l, r, flip in itertools.product((1.5,3.5,5.5),range(4),range(4),range(2)):
        yield Code(threshold=t,children=(Code(base=l),Code(base=r)),flip=flip)
    # All 4^4 leaf assignments on the balanced depth-two routing tree.
    for b in itertools.product(range(4),repeat=4):
        left = Code(threshold=1.5,children=tuple(Code(base=v) for v in b[:2]))
        right = Code(threshold=5.5,children=tuple(Code(base=v) for v in b[2:]))
        yield Code(threshold=3.5,children=(left,right))


def check_forests():
    count = inputs = 0
    max_error = 0.0
    outputs = set()
    temperatures = (0.1,0.25,0.5)
    for code in codes():
        net = compile_code(code)
        extracted = extract_code(net)
        count += 1
        signature=[]
        for x in range(8):
            expected = eval_code(code,x)
            hard = eval_network(net,x)
            assert np.array_equal(hard, np.eye(2)[expected])
            assert eval_extracted(extracted,x) == expected
            for t in temperatures:
                # All gate margins on integer inputs are >= 1.
                assert math.exp(-1/t) < .25
                soft = eval_network(net,x,t)
                error=float(np.abs(soft-np.eye(2)[expected]).max())
                max_error=max(max_error,error)
                assert error <= 1e-12
            signature.append(expected)
            inputs += 1
        outputs.add(tuple(signature))
    assert len(outputs)==256
    return {'networks':count,'inputs_per_network':8,'hard_roundtrip_cases':inputs,
            'distinct_boolean_functions':len(outputs),
            'soft_temperatures':temperatures,'soft_roundtrip_cases':inputs*len(temperatures),
            'minimum_routing_margin':1.0,'soft_max_absolute_error':max_error}


def check_multiway():
    tests=0
    for n in range(2,33):
        for b in range(2,9):
            w=math.ceil((n-1)/(b-1))
            # Disjoint consecutive boundary allocations, at most b-1 per factor.
            groups=[list(range(j*(b-1),min((j+1)*(b-1),n-1))) for j in range(w)]
            enc=lambda r:tuple(sum(r>cut for cut in cuts) for cuts in groups)
            assert len({enc(r) for r in range(n)})==n
            for r,s in itertools.product(range(n),repeat=2):
                assert enc(min(r,s))==tuple(min(x,y) for x,y in zip(enc(r),enc(s)))
            assert (w-1)*(b-1)<n-1<=w*(b-1)
            tests+=1
    return {'chain_sizes':[2,32],'alphabet_sizes':[2,8],'cases':tests}


def main():
    result={'status':'all assertions passed',
            'scope':'finite mathematical and compiled-network checks; no training experiment or Lean compilation',
            'environment':{'python':platform.python_version(),'numpy':np.__version__},
            'quotient':check_read_quotients(),
            'chain':check_chain_exchange(),
            'boolean':check_boolean_exchange(),
            'multiway':check_multiway(),
            'machine_extraction':check_machine_extraction(),
            'forest_extraction':check_forests(),
            'literal_transformer':check_literal_forests(codes(), BASE, eval_code),
            'commutative_monoids':check_monoids(),
            'symbol_hardening':check_symbol_hardening(),
            'coupled_min':check_coupled_min()}
    path=Path(__file__).resolve().parent/'results.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
