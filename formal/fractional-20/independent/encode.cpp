// Independent encoding, written before consulting exp49_frac_core.py.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
struct CNF {
  int nv=0; vector<vector<int>> cs;
  int fresh(){return ++nv;}
  void add(vector<int> c){cs.push_back(move(c));}
  int conj(vector<int> xs) {
    int z=fresh(); for(int x:xs) add({-z,x});
    vector<int> c{z}; for(int x:xs)c.push_back(-x); add(c); return z;
  }
  int disj(vector<int> xs) { for(int &x:xs)x=-x; return -conj(xs); }
  // Full equivalence s[i,j] <-> at least j of x[0..i].
  vector<int> thresholds(const vector<int>& xs,int k){
    vector<int> prev;
    for(int x:xs){
      vector<int> cur(min(k,int(prev.size())+1));
      for(int j=0;j<int(cur.size());++j){
        int z=cur[j]=fresh();
        if(j<int(prev.size())) add({-prev[j],z});
        if(j==0) add({-x,z}); else add({-x,-prev[j-1],z});
        vector<int> c{-z}; if(j<int(prev.size()))c.push_back(prev[j]); c.push_back(x);add(c);
        if(j>0){c={-z,prev[j-1]};if(j<int(prev.size()))c.push_back(prev[j]);add(c);}
      }
      prev=move(cur);
    }
    return prev;
  }
  void atmost(const vector<int>&xs,int k,int guard=0){
    if(int(xs.size())<=k)return;
    auto ts=thresholds(xs,k+1);
    if(guard)add({-guard,-ts[k]});else add({-ts[k]});
  }
  // Lex a >= b. prefix is true precisely when previous entries match.
  void lex_ge(const vector<int>&a,const vector<int>&b,int guard){
    int p=guard;
    for(size_t i=0;i<a.size();++i){
      add({-p,a[i],-b[i]});
      int eq=disj({conj({a[i],b[i]}),conj({-a[i],-b[i]})});
      p=conj({p,eq});
    }
  }
  void save(string path){ofstream f(path);f<<"p cnf "<<nv<<" "<<cs.size()<<"\n";for(auto &c:cs){for(int x:c)f<<x<<" ";f<<"0\n";}}
};
int main(int argc,char**argv){
  if(argc!=5){cerr<<"usage: encode n clique_size local_bound output_prefix\n";return 2;}
  int n=stoi(argv[1]),m=stoi(argv[2]),bound=stoi(argv[3]);string out=argv[4];
  if(n<2||n>40||m<2||bound<0)throw runtime_error("bad parameters");
  CNF f;vector<vector<int>> e(n,vector<int>(n)),q=e;vector<pair<int,int>> pairs;
  for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){e[i][j]=e[j][i]=f.fresh();q[i][j]=q[j][i]=f.fresh();pairs.push_back({i,j});f.add({-q[i][j],e[i][j]});}
  vector<int> qs;for(auto [i,j]:pairs)qs.push_back(q[i][j]);
  auto ts=f.thresholds(qs,m+1); if(int(ts.size())<m)f.add({});else{f.add({ts[m-1]});if(int(ts.size())>m)f.add({-ts[m]});}
  for(int i=0;i<n;i++){
    vector<int> es,active;for(int j=0;j<n;j++)if(i!=j){es.push_back(e[i][j]);active.push_back(q[i][j]);}
    f.atmost(es,4);
    // Every non-isolated vertex belongs to V(Q). Padding vertices are isolated.
    for(int x:es){auto c=active;c.push_back(-x);f.add(c);}
  }
  for(size_t s=0;s<pairs.size();s++)for(size_t r=s+1;r<pairs.size();r++){
    auto [a,b]=pairs[s];auto [c,d]=pairs[r];
    if(a==c||a==d||b==c||b==d)continue;
    f.add({-q[a][b],-q[c][d],e[a][c],e[a][d],e[b][c],e[b][d]});
  }
  for(auto [a,b]:pairs){
    vector<int> inR(n),count;
    for(int v=0;v<n;v++)if(v!=a&&v!=b){
      inR[v]=f.disj({e[a][v],e[b][v]});
      int common=f.conj({e[a][v],e[b][v]});for(int z=0;z<4;z++)count.push_back(common);
    }
    for(auto [c,d]:pairs)if(c!=a&&c!=b&&d!=a&&d!=b)
      count.push_back(f.conj({e[c][d],inR[c],inR[d]}));
    f.atmost(count,bound,q[a][b]);
  }
  // Select any Q edge as 01, orient so deg(0)<=deg(1), label neighbours
  // common first, then 0-only, then 1-only, then vertices outside N[0] U N[1].
  f.add({q[0][1]});vector<int> selectors;
  for(int da=1;da<=4;da++)for(int db=da;db<=4;db++)for(int t=0;t<=min(da-1,db-1);t++){
    if(4*t>bound)continue;
    int w=da+db-t;
    if(w>n||4*(w-2)<m-1)continue;
    int s=f.fresh();selectors.push_back(s);
    for(int v=2;v<n;v++){
      bool ea=v<2+t||(v>=2+t&&v<da+1);
      bool eb=v<2+t||(v>=da+1&&v<w);
      f.add({-s,ea?e[0][v]:-e[0][v]}); f.add({-s,eb?e[1][v]:-e[1][v]});
    }
    // Order outside vertices by their adjacency vectors to the fixed W.
    for(int v=w;v+1<n;v++){
      vector<int>a,b;for(int x=0;x<w;x++){a.push_back(e[v][x]);b.push_back(e[v+1][x]);}
      f.lex_ge(a,b,s);
    }
  }
  f.add(selectors);f.save(out+".cnf");
  ofstream map(out+".map");map<<n<<" "<<m<<" "<<bound<<"\n";
  for(auto [a,b]:pairs)map<<a<<" "<<b<<" "<<e[a][b]<<" "<<q[a][b]<<"\n";
  cout<<"n="<<n<<" m="<<m<<" bound="<<bound<<" variables="<<f.nv<<" clauses="<<f.cs.size()<<" root_cases="<<selectors.size()<<"\n";
}
