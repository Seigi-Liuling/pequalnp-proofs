// Bounded search for task L-meta-523. Build with g++ -O3 -std=c++20.
// Enumerate circuits reachable from seeded cover circuits through single-gate
// edits that preserve the target, and two-gate edits of the first 4000 circuits.
// Completing this search without a witness does not exclude other 11-gate circuits.
// Each truth table has one bit for each minimal true or maximal false input.
//
// Reproduced result with libstdc++: 193 seeds, 13211 reached circuits,
// 7891480311 edits, 1370 nested candidates, all with a reducing lift.
#include <array>
#include <algorithm>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <random>
#include <set>
#include <vector>
using namespace std;
using TruthTable = uint64_t;
using Net=array<int,11>;
// The minimal positive inputs of the graph edge function.
const array<pair<int,int>,8> edges={{{0,1},{1,2},{2,3},{3,4},{4,5},{0,5},{0,6},{1,7}}};
// Encode each gate by its two sorted inputs and one operation bit.
int encodeGate(int a,int b,int c){return min(a,b)+32*max(a,b)+1024*c;}
int a(int g){return g&31;}
int b(int g){return (g>>5)&31;}
bool isAnd(int g){return g>>10;}
array<TruthTable, 19> wireValues;
TruthTable target, negativeMask;
array<vector<int>,11> options;
vector<int> testInputs;
mt19937 rng(523);
bool edge(int x){for(auto [p,q]:edges)if((x>>p&1)&&(x>>q&1))return true;return false;}
void setup(){
 for(auto [p,q]:edges)testInputs.push_back((1<<p)|(1<<q));
 for(int x=0;x<256;x++)if(!edge(x)){
  bool maximal=true;
  for(int i=0;i<8;i++)if(!(x>>i&1)&&!edge(x|(1<<i)))maximal=false;
  if(maximal)testInputs.push_back(x);
 }
 target=255;negativeMask=((1ULL<<testInputs.size())-1)^target;
 for(int i=0;i<8;i++)for(int j=0;j<(int)testInputs.size();j++)if(testInputs[j]>>i&1)wireValues[i]|=1ULL<<j;
 for(int i=0;i<11;i++)for(int p=0;p<8+i;p++)for(int q=p;q<8+i;q++)for(int c=0;c<2;c++)options[i].push_back(encodeGate(p,q,c));
}
// Only recompute the suffix after an edit. Earlier wires retain their values.
TruthTable evaluate(const Net& network,int start=0){
 for(int j=start;j<11;j++){
  int g=network[j];wireValues[j+8]=isAnd(g)?wireValues[a(g)]&wireValues[b(g)]:wireValues[a(g)]|wireValues[b(g)];
 }
 return wireValues[18];
}
// Each gate records which earlier AND gates it can reach.
int nested(const Net& network){
 int count=0;array<unsigned,19> reach{};
 for(int j=0;j<11;j++){
  auto g=network[j];unsigned deps=reach[a(g)]|reach[b(g)];
  if(isAnd(g)){count+=popcount(deps);deps|=1U<<j;}
  reach[8+j]=deps;
 }
 return count;
}
// Audit every reported flattening lift on all 256 inputs.
void auditLift(const Net& original, const Net& edited, int liftedWire) {
    for (int input = 0; input < 256; ++input) {
        array<bool, 19> values{};
        for (int i = 0; i < 8; ++i) values[i] = (input >> i) & 1;
        auto evaluateOnInput = [&](const Net& network) {
            for (int j = 0; j < 11; ++j) {
                int gate = network[j];
                values[8 + j] = isAnd(gate) ? values[a(gate)] && values[b(gate)]
                                           : values[a(gate)] || values[b(gate)];
            }
        };
        evaluateOnInput(original);
        bool expected = edge(input);
        bool liftedValue = values[liftedWire];
        if (values[18] != expected || (liftedValue && !expected)) abort();
        evaluateOnInput(edited);
        if ((values[18] || liftedValue) != expected) abort();
    }
}

// The appended OR cannot create any additional AND-to-AND dependency.
// The lifted operand precedes the edited gate, so the edit cannot change it.
bool isWitness(const Net& network){
 int before=nested(network);
 if(!before)return false;
 evaluate(network);
 auto old=wireValues;
 for(int j=0;j<10;j++)if(!isAnd(network[j])){
  for(auto [p,h]:{pair{a(network[j]),b(network[j])},pair{b(network[j]),a(network[j])}})if(!(old[h]&negativeMask)){
   Net edited=network;edited[j]=encodeGate(p,p,0);
   wireValues=old;
   if ((evaluate(edited, j) | old[h]) == target && nested(edited) < before) {
       auditLift(network, edited, h);
       return false;
   }
  }
 }
 return true;
}
vector<Net> seeds(){
 vector<Net> result;
 for(int orient=0;orient<256;orient++){
  array<vector<int>,8> star;
  for(int j=0;j<8;j++){
   auto [p,q]=edges[j];if(orient>>j&1)swap(p,q);
   star[p].push_back(q);
  }
  int count=0;for(auto& s:star)count+=!s.empty();
  if(count!=4)continue;
  for(int t=0;t<14;t++){
   vector<int> gates,outs,ids={0,1,2,3,4,5,6,7};shuffle(ids.begin(),ids.end(),rng);
   for(int p:ids)if(!star[p].empty()){
    auto s=star[p];shuffle(s.begin(),s.end(),rng);
    int leaf=s[0];for(int i=1;i<(int)s.size();i++){gates.push_back(encodeGate(leaf,s[i],0));leaf=7+gates.size();}
    gates.push_back(encodeGate(p,leaf,1));outs.push_back(7+gates.size());
   }
   while(outs.size()>1){shuffle(outs.begin(),outs.end(),rng);int p=outs.back();outs.pop_back();gates.push_back(encodeGate(p,outs.back(),0));outs.back()=7+gates.size();}
   Net network;copy(gates.begin(),gates.end(),network.begin());
   if(evaluate(network)!=target)abort();
   result.push_back(network);
  }
 }
 return result;
}
int main(){
 setup();auto s=seeds();set<Net> visited(s.begin(),s.end());vector<Net> queue(visited.begin(),visited.end());
 cout<<"tests "<<testInputs.size()<<" seeds "<<queue.size()<<endl;
 uint64_t editCount=0,nestedCount=0;
 for(int i=0;i<(int)queue.size()&&i<180000;i++){
  Net current=queue[i];
  if(nested(current))nestedCount++;
  if(isWitness(current)){
   cout<<"WITNESS";
   for(int g:current)cout<<" "<<isAnd(g)<<":"<<a(g)<<","<<b(g);
   cout<<endl;return 0;
  }
  for(int j=0;j<11;j++){
   evaluate(current);
   Net edited=current;
   for(int g:options[j])if(g!=current[j]){
    ++editCount;edited[j]=g;
    if(evaluate(edited,j)==target&&visited.insert(edited).second)queue.push_back(edited);
    // Also check every two-gate edit of the first 4000 reachable networks.
    if(i>=4000)continue;
    for(int k=j+1;k<11;k++){
     evaluate(edited,j);
     for(int h:options[k])if(h!=current[k]){
      ++editCount;edited[k]=h;
      if(evaluate(edited,k)==target&&visited.insert(edited).second)queue.push_back(edited);
     }
     edited[k]=current[k];
    }
   }
  }
  if((i+1)%20000==0)cout<<"expanded "<<i+1<<" visited "<<visited.size()<<" tests "<<editCount<<" nested "<<nestedCount<<endl;
 }
 cout<<"finished visited "<<visited.size()<<" tests "<<editCount<<" nested "<<nestedCount<<endl;
}
