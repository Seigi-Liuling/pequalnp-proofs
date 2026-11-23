"""Reproduce a bounded obstruction for L-gct-179 (Python 3 and SymPy).

Let F(T) be the sum over injections f from four rows to five columns of
the product of 1+T[i,f(i)]. Let W be the six-dimensional space given by
witnessFun in the upstream L_gct_180.lean, with w a primitive cube root.
If a complex linear space V contains W and F is constant on V, then
dF_u(v)=0 for every u in W and v in V, by differentiating F(u+s*v).

The 32 sample gradients below give a matrix over Q(w). Its rank is 13,
as computed by restriction of scalars to Q (rank 26). Scalar extension
to C preserves rank. Its common kernel thus has dimension seven over C.
Any seven-dimensional extension would equal that kernel. An explicit
kernel vector gives F = 43904/375 instead of 120, excluding the extension.
This does not exclude seven-dimensional spaces that do not contain W.

Reference: brilliant-hq/pequalnp-proofs, f61bf5e, L_gct_180.lean.
"""
from itertools import permutations
from random import Random
import sympy as S

# Exact arithmetic in Q[w], w^2 = -1-w. Each pair represents a+b*w.
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def mul(x,y):
 a,b=x;c,d=y
 return (a*c-b*d,a*d+b*c-b*d)
def neg(x): return (-x[0],-x[1])
one=(1,0);zero=(0,0);w=(0,1);w2=(-1,-1)
def gradient_and_value(t):
 total=zero;grad=[zero]*20
 for f in permutations(range(5),4):
  pos=[5*i+c for i,c in enumerate(f)]
  z=[add(one,t[j]) for j in pos]
  total=add(total,mul(mul(z[0],z[1]),mul(z[2],z[3])))
  for i,j in enumerate(pos):
   grad[j]=add(grad[j],mul(mul(z[(i+1)%4],z[(i+2)%4]),z[(i+3)%4]))
 return grad,total
def known(v):
 x,y,a,b,c,d=[(i,0) for i in v];wx=mul(w,x);wy=mul(w,y);qx=mul(w2,x);qy=mul(w2,y)
 return [x,neg(x),y,neg(y),zero,wx,neg(wx),qy,neg(qy),zero,qx,neg(qx),wy,neg(wy),zero,a,b,c,d,neg(add(add(a,b),add(c,d)))]
# Deterministic small integer samples in the published six-dimensional space.
rng=Random(179);samples=[[rng.randrange(-2,3) for _ in range(6)] for _ in range(32)]
rows=[]
for sample in samples:
 grad,value=gradient_and_value(known(sample));assert value==(120,0)
 first=[];second=[]
 for a,b in grad:
  first.extend((a,-b));second.extend((b,a-b))
 rows.extend([first,second])
A=S.Matrix(rows)
ker=A.nullspace()
print('Q-rank',40-len(ker),'Q-nullity',len(ker))
assert len(ker)==14 # Seven complex dimensions, since the matrix has entries in Q(w).
for q in ker:
 t=list(zip(q[::2],q[1::2]))
 _,value=gradient_and_value(t)
 if value!=(120,0):
  assert A*q == S.zeros(A.rows, 1)
  assert value == (S.Rational(43904,375),0)
  print('direction',t,'permanent',value);break
else: raise RuntimeError('no separating vector found')
