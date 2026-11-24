"""Independent finite audit; the lower bound itself is Lean/kernel checked."""
from itertools import product
# positions0,1 are P0,P1; others are the seven incident line variables.
lines = [0, 12, 4, 10, 1, 5, 11]
expected = {(0,j) for j in (2,3,4,5)} | {(1,j) for j in (2,6,7,8)}
actual = {(p,2+j) for p in (0,1) for j,l in enumerate(lines) if (p-l)%13 in (0,1,3,9)}
assert actual == expected, (actual,expected)
gates = [('or',[2,3]),('or',[9,4]),('or',[10,5]),('and',[0,11]),
         ('or',[2,6]),('or',[13,7]),('or',[14,8]),('and',[1,15]),('or',[12,16])]
def evaluate(x):
    wires = list(x)
    for op,ins in gates:
        assert len(ins) <= 2 and all(i<len(wires) for i in ins)
        values = [wires[i] for i in ins]
        wires.append(all(values) if op=='and' else any(values))
    return wires[17]
for x in product((False,True),repeat=9):
    assert evaluate(x) == any(x[u] and x[v] for u,v in expected)
print('PASS: exact PG(2,3) embedding,8 edges,9 gates,all512 inputs')
