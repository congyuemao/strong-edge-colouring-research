// Graph-level validation independent of the auxiliary CNF variables.
#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**argv){try{
  if(argc!=3)throw runtime_error("usage: check_model prefix output_graph.txt");string p=argv[1];
  ifstream mf(p+".model");if(!mf)throw runtime_error("no model");string line;set<int> yes;bool sat=false;
  while(getline(mf,line)){if(line=="s SATISFIABLE")sat=true;if(line.size()&&line[0]=='v'){istringstream s(line.substr(1));int x;while(s>>x)if(x>0)yes.insert(x);}}
  if(!sat)throw runtime_error("not SAT");
  ifstream mapfile(p+".map");int n,m,bound;mapfile>>n>>m>>bound;
  vector<set<int>> adj(n);vector<pair<int,int>> es,qs;int a,b,e,q;
  while(mapfile>>a>>b>>e>>q){if(yes.count(e)){adj[a].insert(b);adj[b].insert(a);es.push_back({a,b});}if(yes.count(q))qs.push_back({a,b});}
  if(int(qs.size())!=m)throw runtime_error("wrong clique size");for(auto &ns:adj)if(ns.size()>4)throw runtime_error("degree exceeds 4");
  ofstream out(argv[2]);out<<"n="<<n<<" |Q|="<<m<<" bound="<<bound<<"\nE:";for(auto [u,v]:es)out<<" ("<<u<<","<<v<<")";out<<"\nQ:";for(auto [u,v]:qs)out<<" ("<<u<<","<<v<<")";out<<"\n";
  for(auto [u,v]:qs){
    if(!adj[u].count(v))throw runtime_error("selected nonedge");
    int t=0;set<int> r;for(int x:adj[u]){if(adj[v].count(x))t++;r.insert(x);}for(int x:adj[v])r.insert(x);r.erase(u);r.erase(v);
    int ep=0,deg=0;for(auto [x,y]:es){if(r.count(x)&&r.count(y))ep++;if(make_pair(u,v)!=make_pair(x,y)&&(x==u||y==u||x==v||y==v||adj[u].count(x)||adj[u].count(y)||adj[v].count(x)||adj[v].count(y)))deg++;}
    int sum=0;for(int x:r)sum+=int(adj[x].size());if(sum-ep!=deg)throw runtime_error("degree formula mismatch");
    if(4*t+ep>bound)throw runtime_error("local bound violated");
    out<<u<<" "<<v<<": t="<<t<<" e'="<<ep<<" 4t+e'="<<4*t+ep<<" L2degree="<<deg<<"\n";
    for(auto [x,y]:qs)if(x!=u&&x!=v&&y!=u&&y!=v&&!adj[u].count(x)&&!adj[u].count(y)&&!adj[v].count(x)&&!adj[v].count(y))throw runtime_error("nonconflicting pair");
  }
  // Also check every original CNF clause, to detect malformed model parsing.
  ifstream cnf(p+".cnf");getline(cnf,line);int x;bool satisfied=false;long long clauses=0;
  while(cnf>>x){if(x)satisfied|=x>0?yes.count(x)>0:yes.count(-x)==0;else{if(!satisfied)throw runtime_error("CNF clause unsatisfied");satisfied=false;clauses++;}}
  cout<<"VERIFIED SAT: "<<m<<" pairwise conflicting edges; all local bounds <= "<<bound<<"; "<<clauses<<" CNF clauses checked\n";
}catch(const exception&e){cerr<<"REJECTED: "<<e.what()<<"\n";return 1;}}
