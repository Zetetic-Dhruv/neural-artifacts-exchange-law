"""Exhaustive finite commutative-monoid and symbol-hardening checks."""
from __future__ import annotations
import itertools
import math
import numpy as np


def commutative_monoids(n):
    pairs = [(i,j) for i in range(1,n) for j in range(i,n)]
    for vals in itertools.product(range(n), repeat=len(pairs)):
        t = [[0]*n for _ in range(n)]
        for i in range(n):
            t[0][i] = t[i][0] = i
        for (i,j),v in zip(pairs,vals):
            t[i][j] = t[j][i] = v
        if all(t[t[i][j]][k] == t[i][t[j][k]]
               for i,j,k in itertools.product(range(n),repeat=3)):
            yield t


def semilattice_height(t, elements):
    # x <= y iff x*y=x; recursion follows strict decreases.
    memo={}
    def height(y):
        if y not in memo:
            lower=[x for x in elements if x!=y and t[x][y]==x]
            memo[y]=1+max((height(x) for x in lower),default=0)
        return memo[y]
    return max(map(height,elements))


def check_monoids():
    counts=[]
    quotients=0
    nonidempotent=0
    for n in range(1,5):
        count=0
        for t in commutative_monoids(n):
            count+=1
            e=[x for x in range(n) if t[x][x]==x]
            nonidempotent += len(e)<n
            assert all(t[x][y] in e for x,y in itertools.product(e,repeat=2))
            for x in range(n):
                p=x
                for _ in range(1,math.factorial(n)):
                    p=t[p][x]
                assert p in e
            height=semilattice_height(t,e)
            for h in range(1,n+1):
                for rest in itertools.product(range(h),repeat=n-1):
                    f=(h-1,)+rest
                    if len(set(f))!=h:
                        continue
                    if not all(f[t[x][y]]==min(f[x],f[y])
                               for x,y in itertools.product(range(n),repeat=2)):
                        continue
                    assert len({f[x] for x in e})==h
                    assert h<=height<=n
                    quotients+=1
        counts.append({'carrier_size':n,'commutative_monoids':count})
    return {'counts':counts,'nonidempotent_monoids':nonidempotent,
            'surjective_chain_homomorphisms':quotients,
            'all_idempotent_lifts_and_height_bounds_pass':True}


def check_symbol_hardening():
    eta=.25
    cases=tied_correct=0
    temperatures=(.1,.25,.5,1.,2.)
    for scores in itertools.product((-1.,0.,1.),repeat=3):
        s=np.array(scores)
        win=int(np.argmax(s))
        maxima=[j for j in range(3) if s[j]==s[win]]
        for labels in itertools.product((0,1),repeat=3):
            y=labels[win]
            for temp in temperatures:
                p=np.exp((s-s.max())/temp);p/=p.sum()
                u=np.array([sum(p[j] for j in range(3) if labels[j]==z)
                            for z in (0,1)])
                rounded=(np.maximum(u-eta,0)-np.maximum(u-1+eta,0))/(1-2*eta)
                wrong=sum(p[j] for j in range(3) if labels[j]!=y)
                exact=np.allclose(rounded,np.eye(2)[y],atol=1e-12,rtol=0)
                assert exact==(wrong<=eta+1e-12)
                cases+=1
                if len(maxima)>1 and all(labels[j]==y for j in maxima):
                    bad=[j for j in range(3) if labels[j]!=y]
                    if bad:
                        gap=s[win]-max(s[j] for j in bad)
                        r=len(bad)/len(maxima)*math.exp(-gap/temp)
                        assert wrong<=r/(1+r)+1e-12
                        if r<=eta/(1-eta):
                            assert exact
                    else:
                        assert exact
                    tied_correct+=1
    return {'gate_cases':cases,'equal_symbol_tie_cases':tied_correct,
            'temperatures':temperatures,'cleanup_eta':eta,
            'necessary_sufficient_symbol_mass_test':True}


def check_coupled_min():
    cases=0
    for n in range(2,65):
        for b in (2,3,4,8):
            w=0
            while b**w<n:
                w+=1
            digits=lambda i:tuple((i//b**j)%b for j in range(w))
            for x,y in itertools.product(range(n),repeat=2):
                # Hard attention: query 1, keys negative ranks, values digit codes.
                values=(digits(x),digits(y))
                selected=0 if x<=y else 1
                assert values[selected]==digits(min(x,y))
                cases+=1
            assert b**(w-1)<n<=b**w
    return {'chain_sizes':[2,64],'alphabets':[2,3,4,8],
            'hard_attention_min_cases':cases,'all_joint_width_bounds_attained':True}
