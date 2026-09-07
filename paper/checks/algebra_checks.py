#!/usr/bin/env python3
"""Finite checks of proposed inference-quotient and exchange statements.

These are exhaustive checks on stated finite ranges, not Lean proofs, neural
experiments, or checks of the uploaded repository's build. Standard library only.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path


def partitions(n: int):
    """Set partitions in restricted-growth-string representation."""
    if n < 1:
        yield ()
        return
    def grow(prefix, maximum):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for value in range(maximum + 2):
            yield from grow(prefix + [value], max(value, maximum))
    yield from grow([0], 0)


def eq(p, x, y):
    return p[x] == p[y]


def congruence(p, op):
    n = len(p)
    return all(not eq(p, x, y) or eq(p, op(x, z), op(y, z))
               for x in range(n) for y in range(n) for z in range(n))


def joint_injective(p, q):
    return len(set(zip(p, q))) == len(p)


def cardinal(p):
    return len(set(p))


def direct_equivalence(elements, output):
    sig = {u: tuple(output[u & k] for k in elements) for u in elements}
    return {(u, v) for u in elements for v in elements if sig[u] == sig[v]}


def refined_equivalence(elements, output):
    relation = {(u, v) for u in elements for v in elements
                if output[u] == output[v]}
    while True:
        nxt = {(u, v) for u, v in relation
               if all((u & k, v & k) in relation for k in elements)}
        if nxt == relation:
            return relation
        relation = nxt


def check_read_quotients():
    family_count = case_count = 0
    for k in range(1, 4):
        top = (1 << k) - 1
        for bits in range(1 << top):
            elements = [u for u in range(top) if (bits >> u) & 1] + [top]
            members = set(elements)
            if not all(u & v in members for u in elements for v in elements):
                continue
            family_count += 1
            # Every Boolean readout, plus the actual least-survivor readout.
            readouts = [dict(zip(elements, vals)) for vals in
                        itertools.product((0, 1), repeat=len(elements))]
            first_fit = {u: next((j for j in range(k) if (u >> j) & 1), k)
                         for u in elements}
            readouts.append(first_fit)
            for output in readouts:
                relation = direct_equivalence(elements, output)
                assert relation == refined_equivalence(elements, output)
                assert all(output[u] == output[v] for u, v in relation)
                assert all((u & z, v & z) in relation
                           for u, v in relation for z in elements)
                case_count += 1
    return {"candidate_range": [1, 3], "meet_closed_families": family_count,
            "readout_cases": case_count,
            "checks": "suffix equivalence = iterative automaton equivalence; meet congruence; output descends"}


def check_chain_exchange():
    counts = []
    alpha_count = 0
    for n in range(1, 8):
        congs = [p for p in partitions(n) if congruence(p, min)]
        assert len(congs) == 2 ** (n - 1)
        for alpha in congs:
            best = min(cardinal(beta) for beta in congs
                       if joint_injective(alpha, beta))
            assert best == n - cardinal(alpha) + 1
            alpha_count += 1
        counts.append({"chain_states": n, "congruences": len(congs)})
    alpha = (0, 0, 1, 1)
    beta = (0, 1, 1, 2)
    binary_residual = (0, 1, 0, 1)
    assert congruence(alpha, min) and congruence(beta, min)
    assert joint_injective(alpha, beta)
    assert joint_injective(alpha, binary_residual)
    assert not congruence(binary_residual, min)
    return {"range": [1, 7], "structural_quotients_checked": alpha_count,
            "counts": counts, "four_chain": {
                "structure": alpha, "optimal_compositional_residual": beta,
                "static_binary_residual": binary_residual,
                "static_cost": 2, "compositional_cost": 3}}


def check_boolean_exchange():
    cases = []
    for k in range(1, 4):
        n = 1 << k
        congs = [p for p in partitions(n) if congruence(p, lambda x, y: x & y)]
        for s in range(k + 1):
            mask = (1 << s) - 1
            alpha = tuple(u & mask for u in range(n))
            best = min(cardinal(beta) for beta in congs
                       if joint_injective(alpha, beta))
            assert best == 2 ** (k - s)
            cases.append({"bits": k, "structural_bits": s,
                          "residual_states": best})
    return cases


def main():
    results = {"status": "all assertions passed",
               "scope": "finite mathematical checks only; no Lean compilation or neural experiment",
               "read_quotients": check_read_quotients(),
               "chain_exchange": check_chain_exchange(),
               "boolean_exchange": check_boolean_exchange()}
    path = Path(__file__).with_name("finite_check_results.json")
    path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
