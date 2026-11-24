"""Bounded executable prototype, NOT a Lean theorem or official task completion.
Binary read-back AND/OR only. Finite tests support a precise sample-safe hoisting lemma.
"""
import random,json,contextlib,io,sys
sys.dont_write_bytecode = True
from pathlib import Path
with contextlib.redirect_stdout(io.StringIO()):
 import charging_stress as a

def evaluate(n,G,out,masks):
 allbits=(1<<len(masks))-1
 w=[sum(1<<s for s,m in enumerate(masks) if m>>i&1) for i in range(n)]
 for op,x,y in G:w.append(w[x]&w[y] if op=='and' else w[x]|w[y])
 return w

def pairs(n,G):
 anc=[];ands=set();count=0
 for k,(op,x,y) in enumerate(G):
  S=set()
  for v in (x,y):
   if v>=n:S|=anc[v-n]|{v-n}
  if op=='and':count+=len(S&ands);ands.add(k)
  anc.append(S)
 return count,anc

def hoist(n,G,out,i,tidy=True):
 assert 0<=i<len(G) and any(n+i in (x,y) for _,x,y in G[i+1:])
 # Keep the chosen wire's ACTUAL function in a separate saved wire, but use0 in its old readers.
 H=G[:i+1];saved=n+i
 refs=[('w',v) for v in range(n+i+1)];refs[n+i]=('c',False)
 def put(op,x,y):
  if x[0]=='c' and y[0]=='c':return ('c',(x[1] and y[1]) if op=='and' else (x[1] or y[1]))
  if x[0]=='c':
   return y if (x[1] if op=='and' else not x[1]) else x
  if y[0]=='c':
   return x if (y[1] if op=='and' else not y[1]) else y
  if tidy and x==y:return x
  z=('w',n+len(H));H.append((op,x[1],y[1]));return z
 for op,x,y in G[i+1:]:refs.append(put(op,refs[x],refs[y]))
 target=put('or',refs[out],('w',saved))
 assert target[0]=='w' # Safe applications cannot have a constant-true final result on negatives.
 target=target[1]
 if not tidy:return H,target
 live=set()
 def visit(v):
  if v<n or v-n in live:return
  live.add(v-n);_,x,y=H[v-n];visit(x);visit(y)
 visit(target);rename={v:v for v in range(n)};trim=[]
 for k,(op,x,y) in enumerate(H):
  if k in live:rename[n+k]=n+len(trim);trim.append((op,rename[x],rename[y]))
 return trim,rename[target]

rng=random.Random(1692);tested=0
for _ in range(400):
 n=rng.randrange(2,7);s=rng.randrange(4,17);G=[]
 for k in range(s):G.append((rng.choice(('and','or')),rng.randrange(n+k),rng.randrange(n+k)))
 out=n+s-1;oldp,anc=pairs(n,G)
 candidates=[i for i,(op,_,_) in enumerate(G) if op=='and' and any(G[j][0]=='and' and i in anc[j] for j in range(s))]
 if not candidates:continue
 i=rng.choice(candidates);H,o=hoist(n,G,out,i)
 masks=list(range(1<<n));old=evaluate(n,G,out,masks);new=evaluate(n,H,o,masks)
 assert new[o]==(old[out]|old[n+i])
 assert len(H)<=len(G) and pairs(n,H)[0]<oldp
 # Match the existing Elim pass more closely: no idempotence or dead-code pruning.
 raw,ro=hoist(n,G,out,i,tidy=False)
 assert evaluate(n,raw,ro,masks)[ro]==(old[out]|old[n+i])
 assert len(raw)<=len(G) and pairs(n,raw)[0]<oldp
 tested+=1

def normalize(G,out,tidy=True):
 steps=[]
 while True:
  _,anc=pairs(26,G);w=evaluate(26,G,out,a.samples)
  safe=[i for i,(op,_,_) in enumerate(G) if op=='and' and w[26+i]>>52==0]
  cand=[i for i in safe if any(G[j][0]=='and' and i in anc[j] for j in range(len(G)))]
  if not cand:return G,out,steps
  i=cand[0];old=len(G);oldp=pairs(26,G)[0];H,o=hoist(26,G,out,i,tidy=tidy)
  assert len(H)<=old and pairs(26,H)[0]<oldp
  assert evaluate(26,H,o,a.samples)[o]==a.sample_target
  steps.append({'chosen_AND':i,'old_size':old,'new_size':len(H),'old_AND_pairs':oldp,'new_AND_pairs':pairs(26,H)[0]})
  G,out=H,o

# Full-function redundant example: F AND (F OR (L0 OR L1)).
G,F=a.stars('points');G+= [('or',13,14),('or',F,90),('and',F,91)];out=92
H,o,steps=normalize(G,out)
assert len(G)==67 and len(H)==64 and len(steps)==13
r1={'start_size':67,'end_size':len(H),'steps':steps}
raw,ro,rawsteps=normalize(G,out,tidy=False)
assert len(raw)==65 and pairs(26,raw)[0]==0
r1['Elim_style_no_dead_prune_size']=len(raw)
r1['Elim_style_no_dead_prune_AND_pairs']=pairs(26,raw)[0]
# A safe internal AND need not lie below the FULL output function.
# G=L0 AND L4 AND L10; old output F OR (P0 AND G), which equals F globally.
G,F=a.stars('points');G += [('and',13,17),('and',90,23),('and',0,91),('or',F,92)];out=93
witness=(1<<13)|(1<<17)|(1<<23)
assert evaluate(26,G,out,[witness])[out]==0
assert evaluate(26,G,out,[witness])[91]==1
H,o,steps=normalize(G,out)
assert len(G)==68 and len(H)==67 and len(steps)==1
assert evaluate(26,H,o,[witness])[o]==1
r2={'start_size':68,'end_size':len(H),'steps':steps,'full_function_changes_at_line_triple':True,'all286_samples_preserved':True,'unsafe_nested_AND_pair_remaining':pairs(26,H)[0]}
result={'random_seed':1692,'random_full_truth_table_cases_passed':tested,'attempted_random_circuits':400,'each_selected_case_checked_both_tidy_and_Elim_style':True,'absorption67':r1,'sample_only_safe68':r2,
 'status':'finite executable tests only; generic compiler correctness and AND-pair injection NOT Lean-proved'}
print(json.dumps(result,indent=2));Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
