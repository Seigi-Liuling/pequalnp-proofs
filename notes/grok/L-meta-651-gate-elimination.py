"""Bounded analysis of L-meta-651, proof shard 2 (not a formal lower bound proof).

Compute the strongest recursive numerical bound obtained by:
  * essential-support lower bound support(f)-1;
  * the known exact forest graph-function formula |A|+|E|+tau-1;
  * eliminating one gate per fixed essential variable, only when the child
    restriction remains nonconstant (the hypothesis of project L014).

States represent OR(A) OR edge(G[R]); isolated vertices in R are discarded.
Both values of every essential variable are tried, with memoization.
This is an analysis of this proof template, NOT an exhaustive circuit search.
"""
from functools import lru_cache
from itertools import combinations,product
import json,time
from pathlib import Path
N=10
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
NB=[0]*N
for u,v in EDGES: NB[u]|=1<<v;NB[v]|=1<<u
ALL=(1<<N)-1

def vertices(m): return [i for i in range(N) if m>>i&1]
def edge_count(R): return sum(1 for u,v in EDGES if R>>u&1 and R>>v&1)
def prune(R): return sum(1<<v for v in vertices(R) if NB[v]&R)
def forest(R):
 seen=set()
 def dfs(v,p):
  seen.add(v)
  for u in vertices(NB[v]&R):
   if u==p: continue
   if u in seen or not dfs(u,v): return False
  return True
 return all(v in seen or dfs(v,-1) for v in vertices(R))
@lru_cache(None)
def alpha(R):
 if not R:return 0
 v=(R&-R).bit_length()-1
 return max(alpha(R&~(1<<v)),1+alpha(R&~((1<<v)|NB[v])))
def canonical(A,R): return A,prune(R&~A)
CHOSEN={}
STATES=set()
@lru_cache(None)
def lower(A,R):
 assert (A,R)==canonical(A,R)
 STATES.add((A,R))
 support=A.bit_count()+R.bit_count()
 if support==0:return 0
 base=support-1
 reason={'rule':'support','bound':base}
 if forest(R):
  exact=A.bit_count()+edge_count(R)+(R.bit_count()-alpha(R))-1
  if exact>=base:base=exact;reason={'rule':'forest_formula','bound':base}
 best=base
 for v in vertices(A|R):
  for b in (False,True):
   if A>>v&1:
    if b:continue # constant true, not a nonconstant L014 child
    child=canonical(A&~(1<<v),R)
   elif b:
    newA=A|(NB[v]&R)
    child=canonical(newA,R&~(1<<v)&~newA)
   else:
    child=canonical(A,R&~(1<<v))
   if child==(0,0):continue # constant false, not a nonconstant L014 child
   bound=1+lower(*child)
   if bound>best:
    best=bound;reason={'rule':'one_gate_elimination','vertex':v,'fixed':b,'child':list(child),'bound':bound}
 CHOSEN[(A,R)]=reason
 return best

def function(A,R,x): return any(x>>v&1 for v in vertices(A)) or any(R>>u&1 and R>>v&1 and x>>u&1 and x>>v&1 for u,v in EDGES)

def upper_witness(T):
 gates=[]
 def add(op,ins):
  idx=N+len(gates);gates.append((op,ins));return idx
 def OR(ins):
  cur=ins[0]
  for x in ins[1:]:cur=add('or',[cur,x])
  return cur
 owned={t:[] for t in T}
 for u,v in EDGES:
  if u in T:owned[u].append(v)
  else: assert v in T;owned[v].append(u)
 terms=[]
 for t in T:
  assert owned[t]
  terms.append(add('and',[t,OR(owned[t])]))
 out=OR(terms)
 return gates,out,owned

def eval_circuit(gates,out,x):
 w=[bool(x>>i&1) for i in range(N)]
 for op,ins in gates:w.append((all if op=='and' else any)(w[i] for i in ins))
 return w[out]

start=time.monotonic()
cover_masks=[m for m in range(1<<N) if all(m>>u&1 or m>>v&1 for u,v in EDGES)]
tau=min(m.bit_count() for m in cover_masks)
minimum_covers=[m for m in cover_masks if m.bit_count()==tau]
T=vertices(minimum_covers[0]);gates,out,owned=upper_witness(T)
assert len(gates)==20
assert all(eval_circuit(gates,out,x)==function(0,ALL,x) for x in range(1<<N))
bound=lower(0,ALL)
chain=[];state=(0,ALL)
while True:
 reason=CHOSEN[state];chain.append({'A':vertices(state[0]),'R':vertices(state[1]),**reason})
 if reason['rule']!='one_gate_elimination':break
 state=tuple(reason['child'])
# Verify the state restriction identity for every visited state and every valuation,
# sampled only on the chosen bound chain (finite exact check, not all states).
for item in chain:
 if item['rule']!='one_gate_elimination':continue
 A=sum(1<<v for v in item['A']);R=sum(1<<v for v in item['R']);v=item['vertex'];b=item['fixed'];child=item['child']
 assert all(function(A,R,(x|(1<<v)) if b else (x&~(1<<v)))==function(*child,x) for x in range(1<<N))
# Independently check EVERY memoized state's essential support and restriction
# identities as 1024-bit truth tables, not merely the best-chain examples.
BIT_TRUTH=[sum(1<<x for x in range(1<<N) if x>>v&1) for v in range(N)]
FULL_TRUTH=(1<<(1<<N))-1
@lru_cache(None)
def truth(A,R):
 t=0
 for v in vertices(A):t|=BIT_TRUTH[v]
 for u,v in EDGES:
  if R>>u&1 and R>>v&1:t|=BIT_TRUTH[u]&BIT_TRUTH[v]
 return t
checked_restrictions=0
for A,R in STATES:
 t=truth(A,R)
 for v in vertices(A|R):
  z=t&(FULL_TRUTH^BIT_TRUTH[v]);z|=z<<(1<<v)
  o=t&BIT_TRUTH[v];o|=o>>(1<<v)
  assert z!=o
  child0=canonical(A&~(1<<v),R) if A>>v&1 else canonical(A,R&~(1<<v))
  assert z==truth(*child0)
  if A>>v&1:
   assert o==FULL_TRUTH
  else:
   newA=A|(NB[v]&R)
   child1=canonical(newA,R&~(1<<v)&~newA)
   assert o==truth(*child1)
  checked_restrictions+=2

# Explicit automorphism enumeration, preserving adjacency and nonadjacency.
AUTOS=[]
def backtrack(mapping,used):
 if len(mapping)==N:
  AUTOS.append(tuple(mapping[i] for i in range(N)));return
 unassigned=[v for v in range(N) if v not in mapping]
 v=max(unassigned,key=lambda v:sum(1 for q in mapping if NB[v]>>q&1))
 for u in range(N):
  if u in used:continue
  if all(bool(NB[v]>>q&1)==bool(NB[u]>>w&1) for q,w in mapping.items()):
   mapping[v]=u;used.add(u);backtrack(mapping,used);used.remove(u);del mapping[v]
backtrack({},set())
assert len(AUTOS)==120
assert all(len({a[v] for a in AUTOS})==10 for v in range(N))
first_restrictions=[]
for v in range(N):
 child0=canonical(0,ALL&~(1<<v));newA=NB[v]
 child1=canonical(newA,ALL&~(1<<v)&~newA)
 first_restrictions.append({'vertex':v,'fix_false_child_bound':lower(*child0),'fix_true_child_bound':lower(*child1)})
report={'task':'L-meta-651','shard':2,'n':N,'edges':len(EDGES),'minimum_vertex_cover':tau,'independence_number':alpha(ALL),'number_minimum_vertex_covers':len(minimum_covers),'known_upper_size':len(gates),'upper_checked_inputs':1<<N,'upper_cover':T,'upper_gates':gates,'upper_output':out,'one_gate_elimination_plus_forest_support_bound':bound,'remaining_gap_to_task_lower_bound':20-bound,'memoized_states':lower.cache_info().currsize,'best_template_chain':chain,'elapsed_seconds':round(time.monotonic()-start,3),'formal_proof_of_task':False,'truth_table_restriction_identities_checked':checked_restrictions,'automorphisms':len(AUTOS),'vertex_transitive':True,'first_restriction_bounds':first_restrictions}
Path(__file__).with_suffix('.result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
