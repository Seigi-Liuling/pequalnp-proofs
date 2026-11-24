"""Counterexample to a NAIVE restriction-survival charging invariant, not to1692.
Pruning uses constants, idempotency, and dead-code elimination; NOT absorption.
All counts are finite computations, not formal lower bounds.
"""
from itertools import combinations
D={0,1,3,9}
gates=[]
def gate(op,a,b):
    w=26+len(gates);gates.append((op,a,b));return w
stars=[]
for p in range(13):
    ns=[13+l for l in range(13) if (p-l)%13 in D]
    t=ns[0]
    for w in ns[1:]: t=gate('or',t,w)
    stars.append(gate('and',p,t))
out=stars[0]
for w in stars[1:]: out=gate('or',out,w)
assert len(gates)==64
f=out
h=gate('or',13,14)
v=gate('or',f,h)
out=gate('and',f,v)
assert len(gates)==67
# f AND (f OR h) = f identically: a valid redundant separator, not a64-bound counterexample.
def live_count(pair,n,output):
    lines={l for p in pair for l in range(13) if (p-l)%13 in D}
    wires=[('in',i) if (i in pair if i<13 else i-13 in lines) else False for i in range(26)]
    defs={}
    for k,(op,a,b) in enumerate(gates[:n]):
        x,y=wires[a],wires[b]
        if op=='and':
            z=False if x is False or y is False else y if x is True else x if y is True or x==y else ('gate',k)
        else:
            z=True if x is True or y is True else y if x is False else x if y is False or x==y else ('gate',k)
        if z==('gate',k):defs[k]=(x,y)
        wires.append(z)
    reached=set()
    def visit(z):
        if isinstance(z,tuple) and z[0]=='gate' and z[1] not in reached:
            reached.add(z[1]);x,y=defs[z[1]];visit(x);visit(y)
    visit(wires[output]);return len(reached)
pairs=list(combinations(range(13),2))
a=[live_count(p,64,f) for p in pairs]
b=[live_count(p,67,out) for p in pairs]
assert set(a)=={9} and sum(a)==702
assert sum(b)==849 and 12*67-66==738 and sum(b)>738
# For any distinct lines:12 windows contain their intersection point;9 other windows hit both.
for l,m in pairs:
    A={p for p in range(13) if (p-l)%13 in D};B={p for p in range(13) if (p-m)%13 in D}
    assert len(A&B)==1
    both=[p for p in pairs if set(p)&A and set(p)&B]
    safe=[p for p in both if set(p)&(A&B)]
    assert (len(both),len(safe),len(both)-len(safe))==(21,12,9)
print('PASS:64-gate canonical window sum702; absorption-equivalent67-gate sum849 > candidate738')
print('PASS:all78 line pairs have21 active windows =12 intersection-point +9 cross-private')
