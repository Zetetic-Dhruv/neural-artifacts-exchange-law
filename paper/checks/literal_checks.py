"""Literal shared masked-attention/ReLU implementation of finite forests.

No source code is consulted during forward execution. Every block consists of
shared projection matrices, an attention mask, and shared FFN weight matrices.
"""
from __future__ import annotations
from dataclasses import dataclass
import numpy as np


@dataclass
class Layer:
    wq: np.ndarray
    wk: np.ndarray
    wv: np.ndarray
    wo: np.ndarray
    mask: np.ndarray
    w1: np.ndarray
    b1: np.ndarray
    w2: np.ndarray


@dataclass
class Artifact:
    protected: np.ndarray
    pre_w1: np.ndarray
    pre_b1: np.ndarray
    pre_w2: np.ndarray
    layers: list[Layer]
    x_start: int
    query_start: int
    payload_start: int
    scratch_start: int
    root: int


def compile_literal(code, base: np.ndarray, eta: float = .25) -> Artifact:
    if not 0 < eta < .5:
        raise ValueError('eta must lie strictly between 0 and 1/2.')
    nodes = []
    def visit(c, key=(0., 0.)):
        children = []
        if c.base is not None:
            height = 0
        else:
            t = c.threshold
            children = [visit(c.children[0], (t, -1.)),
                        visit(c.children[1], (-t, 1.))]
            height = 1 + max(nodes[j]['height'] for j in children)
        nodes.append(dict(code=c, key=key, height=height, children=children))
        return len(nodes)-1
    root = visit(code)
    n = len(nodes)
    xs, qs, ks, ps, ss = n, n+8, n+10, n+12, n+14
    dim = n+16
    protected = np.zeros((n, dim))
    protected[:, :n] = np.eye(n)
    for v, node in enumerate(nodes):
        protected[v, ks:ks+2] = node['key']
    # Shared initial FFN: conjunction of token ID and one-hot input.
    pre1, preb, pre2 = [], [], []
    for v, node in enumerate(nodes):
        for x in range(8):
            w = np.zeros(dim); w[v] = w[xs+x] = 1
            o = np.zeros(dim)
            y = int(base[node['code'].base, x]) if node['code'].base is not None else 0
            o[ps+y] = 1
            pre1.append(w); preb.append(-1); pre2.append(o)
    layers = []
    for h in range(1, nodes[root]['height']+1):
        wq = np.zeros((2, dim)); wq[:, qs:qs+2] = np.eye(2)
        wk = np.zeros((2, dim)); wk[:, ks:ks+2] = np.eye(2)
        wv = np.zeros((2, dim)); wv[:, ps:ps+2] = np.eye(2)
        wo = np.zeros((dim, 2)); wo[ss:ss+2] = np.eye(2)
        mask = np.zeros((n,n), dtype=bool)
        rows, biases, cols = [], [], []
        for v, node in enumerate(nodes):
            active = node['height'] == h
            mask[v, node['children'] if active else [v]] = True
            if not active:
                continue
            for j in range(2):
                # Two ReLUs implement token-gated symbolic correction.
                for bias, coeff in ((-1-eta, 1/(1-2*eta)),
                                    (-2+eta, -1/(1-2*eta))):
                    w = np.zeros(dim); w[v] = w[ss+j] = 1
                    o = np.zeros(dim); o[ps+(j ^ node['code'].flip)] = coeff
                    rows.append(w); biases.append(bias); cols.append(o)
                # Residual overwrite: subtract this active token's old payload.
                w = np.zeros(dim); w[v] = w[ps+j] = 1
                o = np.zeros(dim); o[ps+j] = -1
                rows.append(w); biases.append(-1); cols.append(o)
        # Shared scratch reset, valid for every token.
        for j in range(2):
            w = np.zeros(dim); w[ss+j] = 1
            o = np.zeros(dim); o[ss+j] = -1
            rows.append(w); biases.append(0); cols.append(o)
        layers.append(Layer(wq,wk,wv,wo,mask,np.array(rows),np.array(biases),
                            np.array(cols).T))
    return Artifact(protected,np.array(pre1),np.array(preb),np.array(pre2).T,
                    layers,xs,qs,ps,ss,root)


def execute(net: Artifact, x: int, temperature: float) -> tuple[np.ndarray, float]:
    z = net.protected.copy()
    z[:,net.x_start+x] = 1
    z[:,net.query_start:net.query_start+2] = (1,x)
    frozen = z[:,:net.payload_start].copy()
    z += np.maximum(z @ net.pre_w1.T + net.pre_b1, 0) @ net.pre_w2.T
    largest_invariant_error = 0.
    for layer in net.layers:
        scores = (z @ layer.wq.T) @ (z @ layer.wk.T).T
        scores = np.where(layer.mask, scores, -np.inf)
        if temperature == 0:
            weights = np.eye(len(z))[np.argmax(scores, axis=1)]
        else:
            shifted = (scores-scores.max(axis=1, keepdims=True))/temperature
            weights = np.exp(shifted)
            weights /= weights.sum(axis=1, keepdims=True)
        z = z + (weights @ (z @ layer.wv.T)) @ layer.wo.T
        z = z + np.maximum(z @ layer.w1.T + layer.b1, 0) @ layer.w2.T
        assert np.array_equal(z[:,:net.payload_start], frozen)
        payload = z[:,net.payload_start:net.payload_start+2]
        nearest = np.eye(2)[np.argmax(payload,axis=1)]
        error = max(float(np.abs(payload-nearest).max()),
                    float(np.abs(z[:,net.scratch_start:net.scratch_start+2]).max()))
        largest_invariant_error = max(largest_invariant_error,error)
        assert error <= 1e-12
    return z[net.root,net.payload_start:net.payload_start+2], largest_invariant_error


def check_literal_forests(code_iterator, base: np.ndarray, reference) -> dict:
    count = cases = 0
    max_error = invariant_error = 0.
    for code in code_iterator:
        net = compile_literal(code,base)
        count += 1
        for x in range(8):
            target = np.eye(2)[reference(code,x)]
            for temperature in (0., .1, .25, .5):
                result, err = execute(net,x,temperature)
                error = float(np.abs(result-target).max())
                max_error = max(max_error,error)
                invariant_error = max(invariant_error,err)
                assert error <= 1e-12
                cases += 1
    return {'artifacts':count, 'network_input_temperature_cases':cases,
            'temperatures':[0.,.1,.25,.5], 'max_absolute_error':max_error,
            'max_codebook_or_scratch_error':invariant_error,
            'shared_projections_and_ffns':True,
            'protected_coordinates_unchanged':True}
