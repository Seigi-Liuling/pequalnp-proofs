"""Finite pressure tests for a candidate1692 charging inequality.
No solver. No claim of an official lower-bound proof.
"""
from itertools import combinations
from collections import Counter
from pathlib import Path
import json
D={0,1,3,9}
P=range(13);pairs=list(combinations(P,2))
positives=[(1<<p)|(1<<(13+l)) for p in P for l in P if (p-l)%13 in D]
negatives=[]
for Q in combinations(P,4):
 if all(sum((p-l)%13 in D for p in Q)<=2 for l in P):
  negatives.append(sum(1<<p for p in Q)+sum(1<<(13+l) for l in P if all((p-l)%13 not in D for p in Q)))
assert len(positives)==52 and len(negatives)==234
samples=positives+negatives
sample_target=(1<<len(positives))-1

def stars(side):
 gates=[]
 def add(op,a,b):
  w=26+len(gates);gates.append((op,a,b));return w
 roots=[]
 for c in P:
  if side=='points':
   ins=[13+l for l in P if (c-l)%13 in D];center=c
  else:
   ins=[p for p in P if (p-c)%13 in D];center=13+c
  t=ins[0]
  for v in ins[1:]:t=add('or',t,v)
  roots.append(add('and',center,t))
 out=roots[0]
 for w in roots[1:]:out=add('or',out,w)
 assert len(gates)==64
 return gates,out

def table_eval(gates,out,masks,override=None):
 allbits=(1<<len(masks))-1
 wires=[sum(1<<s for s,m in enumerate(masks) if m>>i&1) for i in range(26)]
 for k,(op,a,b) in enumerate(gates):
  if override and k==override[0]:
   mode=override[1];z=0 if mode=='zero' else allbits if mode=='one' else wires[a if mode=='a' else b]
  else:z=wires[a]&wires[b] if op=='and' else wires[a]|wires[b]
  wires.append(z)
 return wires[out]

def local_live(gates,out,pair,side='points',semantic=True):
 if side=='points':
  keep=list(pair)+[13+l for l in P if any((p-l)%13 in D for p in pair)]
 else:
  keep=[p for p in P if any((p-l)%13 in D for l in pair)]+[13+l for l in pair]
 assert len(keep)==9
 vals=[0]*26
 for j,i in enumerate(keep):vals[i]=sum(1<<s for s in range(512) if s>>j&1)
 ones=(1<<512)-1
 # Exact truth-table semantic aliasing of ALL earlier wires, plus dead-code elimination.
 wires=[('in',i) if vals[i] else False for i in range(26)]
 seen={0:False,ones:True}
 for i,v in enumerate(vals):seen.setdefault(v,wires[i])
 defs={}
 for k,(op,a,b) in enumerate(gates):
  v=vals[a]&vals[b] if op=='and' else vals[a]|vals[b]
  if semantic and v in seen:z=seen[v]
  else:
   x,y=wires[a],wires[b]
   if op=='and':z=False if x is False or y is False else y if x is True else x if y is True or x==y else ('gate',k)
   else:z=True if x is True or y is True else y if x is False else x if y is False or x==y else ('gate',k)
   if z==('gate',k):defs[k]=(x,y)
  vals.append(v);wires.append(z);seen.setdefault(v,z)
 reached=set()
 def visit(z):
  if isinstance(z,tuple) and z[0]=='gate' and z[1] not in reached:
   reached.add(z[1]);x,y=defs[z[1]];visit(x);visit(y)
 visit(wires[out])
 # Re-evaluate the retained representative DAG independently of the original wire fold.
 memo={}
 def eval_alias(z):
  if z is False:return 0
  if z is True:return ones
  typ,k=z
  if typ=='in':return sum(1<<t for t in range(512) if t>>keep.index(k)&1)
  if k not in memo:
   x,y=defs[k]
   assert x is not False and x is not True and y is not False and y is not True
   vx,vy=eval_alias(x),eval_alias(y)
   memo[k]=vx&vy if gates[k][0]=='and' else vx|vy
  return memo[k]
 assert eval_alias(wires[out])==vals[out]
 assert len(reached)>=9
 return len(reached)

results={}
for side in ('points','lines'):
 gates,out=stars(side)
 assert table_eval(gates,out,samples)==sample_target
 bypass=[]
 for k in range(64):
  for mode in ('zero','one','a','b'):
   if table_eval(gates,out,samples,(k,mode))==sample_target:bypass.append([k,mode])
 assert not bypass
 R={s:[local_live(gates,out,p,s) for p in pairs] for s in ('points','lines')}
 results[side]={'gates':64,'sample_correct':True,'single_gate_bypasses_preserving286samples':bypass,
  'R_point':sum(R['points']),'R_line':sum(R['lines']),
  'point_window_distribution':dict(Counter(R['points'])),'line_window_distribution':dict(Counter(R['lines']))}
 assert (sum(R['points']),sum(R['lines']))==((702,1092) if side=='points' else (1092,702))
# Mixed star covers: move k edges at P0 from line-stars into one extra point-star.
# Still exactly the incidence function;65 gates and no one-gate sample bypass.
for k in range(1,5):
 K=[l for l in P if (0-l)%13 in D][:k]
 G=[]
 def mk(op,a,b):
  w=26+len(G);G.append((op,a,b));return w
 roots=[]
 for l in P:
  ins=[p for p in P if (p-l)%13 in D and not(p==0 and l in K)]
  t=ins[0]
  for p in ins[1:]:t=mk('or',t,p)
  roots.append(mk('and',13+l,t))
 t=13+K[0]
 for l in K[1:]:t=mk('or',t,13+l)
 roots.append(mk('and',0,t))
 out=roots[0]
 for w in roots[1:]:out=mk('or',out,w)
 assert len(G)==65 and table_eval(G,out,samples)==sample_target
 bypass=[]
 for g in range(65):
  for mode in ('zero','one','a','b'):
   if table_eval(G,out,samples,(g,mode))==sample_target:bypass.append([g,mode])
 assert not bypass
 Rp=sum(local_live(G,out,p,'points') for p in pairs)
 Rl=sum(local_live(G,out,p,'lines') for p in pairs)
 assert Rp==1104-9*k
 assert Rl==702+78-(13-k)*(12-k)//2
 results['mixed_move_'+str(k)]={'gates':65,'sample_correct':True,
  'single_gate_bypasses_preserving286samples':bypass,'R_point':Rp,'R_line':Rl,
  'minimum_of_orientations':min(Rp,Rl),'candidate_RHS':714}
# Add a sample-safe, point-free threshold4 on the13 line inputs.
gates,out=stars('points');F=out
def add(op,a,b):
 w=26+len(gates);gates.append((op,a,b));return w
prev={}
for i in range(1,14):
 new={}
 for j in range(1,min(i,4)+1):
  x=13+i-1
  if j==1:new[j]=x if i==1 else add('or',prev[1],x)
  elif j==i:new[j]=add('and',prev[j-1],x)
  else:new[j]=add('or',prev[j],add('and',prev[j-1],x))
 prev=new
H=prev[4];out=add('or',F,H)
# Remove globally unused DP states and remap indices without changing the function.
live=set()
def visit(w):
 if w<26 or w-26 in live:return
 live.add(w-26);_,a,b=gates[w-26];visit(a);visit(b)
visit(out);rename={i:i for i in range(26)};trim=[]
for k,(op,a,b) in enumerate(gates):
 if k in live:rename[26+k]=26+len(trim);trim.append((op,rename[a],rename[b]))
out=rename[out];gates=trim
assert table_eval(gates,out,samples)==sample_target
R=[local_live(gates,out,p) for p in pairs]
results['sample_safe_threshold4_junk']={'gates':len(gates),'sample_correct':True,'R_point':sum(R),'candidate_RHS':12*len(gates)-66,'window_distribution':dict(Counter(R)),
 'root_bypass_to_F_preserves_samples':table_eval(gates,out,samples,(out-26,'a'))==sample_target}
assert sum(R)>12*len(gates)-66
print(json.dumps(results,indent=2))
Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2)+'\n')
