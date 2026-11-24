"""Simpler delete-one-reader-and-append-OR prototype. NOT a Lean proof."""
import random,json,contextlib,io,sys
sys.dont_write_bytecode=True
from pathlib import Path
with contextlib.redirect_stdout(io.StringIO()):
 import charging_stress as a
 import safe_hoist_stress as b

def last_and(G):return max([k+1 for k,(op,_,_) in enumerate(G) if op=='and'],default=0)
def lift(n,G,out,g):
 assert 0<=g<len(G) and out<n+len(G)
 j=next(j for j in range(g+1,len(G)) if n+g in G[j][1:])
 op,x,y=G[j]
 redirect=n+g if op=='and' else (y if x==n+g else x)
 def rd(w):return redirect if w==n+j else w-1 if w>n+j else w
 H=G[:j]+[(op,rd(x),rd(y)) for op,x,y in G[j+1:]]
 H.append(('or',rd(out),n+g))
 return H,n+len(H)-1,j

rng=random.Random(1692);tested=0;pair_non_decreasing=0
for _ in range(400):
 n=rng.randrange(2,7);s=rng.randrange(4,17);G=[]
 for k in range(s):G.append((rng.choice(('and','or')),rng.randrange(n+k),rng.randrange(n+k)))
 out=n+s-1;oldp,anc=b.pairs(n,G)
 cand=[i for i,(op,_,_) in enumerate(G) if op=='and' and any(G[j][0]=='and' and i in anc[j] for j in range(s))]
 if not cand:continue
 g=rng.choice(cand);H,o,j=lift(n,G,out,g)
 masks=list(range(1<<n));old=b.evaluate(n,G,out,masks);new=b.evaluate(n,H,o,masks)
 assert new[o]==old[out]|old[n+g]
 assert len(H)==len(G) and last_and(H)<last_and(G)
 assert all(x<n+k and y<n+k for k,(_,x,y) in enumerate(H))
 pair_non_decreasing+=b.pairs(n,H)[0]==oldp
 tested+=1
# A diamond shows that a SINGLE local lift need not strictly decrease AND-pair count.
G=[('and',0,1),('or',4,2),('or',4,3),('and',5,6)]
H,o,j=lift(4,G,7,0)
assert b.pairs(4,G)[0]==b.pairs(4,H)[0]==1
assert (last_and(G),last_and(H))==(4,3)

def normalize(G,out):
 steps=[];initial=len(G)
 while True:
  _,anc=b.pairs(26,G);w=b.evaluate(26,G,out,a.samples)
  cand=[g for g,(op,_,_) in enumerate(G) if op=='and' and w[26+g]>>52==0
        and any(G[j][0]=='and' and g in anc[j] for j in range(len(G)))]
  if not cand:return G,out,steps
  g=cand[0];H,o,j=lift(26,G,out,g)
  assert len(H)==initial and last_and(H)<last_and(G)
  assert b.evaluate(26,H,o,a.samples)[o]==a.sample_target
  steps.append({'saved_AND':g,'deleted_reader':j,'old_last_AND':last_and(G),'new_last_AND':last_and(H)})
  G,out=H,o
  assert len(steps)<=initial

G,F=a.stars('points');G+=[('or',13,14),('or',F,90),('and',F,91)];out=92
H,o,steps=normalize(G,out)
assert len(H)==67 and b.pairs(26,H)[0]==0
r1={'size':67,'steps':steps,'end_AND_pairs':b.pairs(26,H)[0]}
G,F=a.stars('points');G+=[('and',13,17),('and',90,23),('and',0,91),('or',F,92)];out=93
H,o,steps=normalize(G,out)
assert len(H)==68 and b.pairs(26,H)[0]==1
r2={'size':68,'steps':steps,'end_unsafe_AND_pairs':b.pairs(26,H)[0]}
result={'status':'finite tests only; no generic Lean theorem','random_selected_cases':tested,
 'random_cases_where_AND_pair_count_did_NOT_strictly_decrease':pair_non_decreasing,
 'last_AND_position_strictly_decreased_in_every_selected_case':True,
 'diamond_AND_pairs_old_new':[1,1],'diamond_last_AND_old_new':[4,3],
 'absorption67':r1,'sample_only68':r2}
print(json.dumps(result,indent=2));Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
