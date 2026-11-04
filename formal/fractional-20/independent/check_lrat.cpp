// Standalone checker for the RUP fragment of LRAT. Rejects all RAT steps.
// No solver code or solver libraries are used.
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
struct Clause { vector<int> lits; bool live=false; };
struct Checker {
  vector<Clause> db{1}; vector<signed char> val;vector<int> trail;
  long long rup=0,del=0; bool empty=false;int maxid=0;
  int value(int l){if(!l||size_t(abs(l))>=val.size())throw runtime_error("literal out of range");return l>0?val[l]:-val[-l];}
  bool set(int l){int v=value(l);if(v)return v>0;val[abs(l)]=l>0?1:-1;trail.push_back(abs(l));return true;}
  void undo(size_t k){while(trail.size()>k){val[trail.back()]=0;trail.pop_back();}}
  const vector<int>& get(int id){if(id<=0||size_t(id)>=db.size()||!db[id].live)throw runtime_error("missing/deleted antecedent "+to_string(id));return db[id].lits;}
  void add(int id,vector<int> c){
    if(id<=maxid)throw runtime_error("non-increasing clause id");maxid=id;if(size_t(id)>=db.size())db.resize(size_t(id)+1);
    for(int l:c)value(l);
    db[id]={move(c),true};if(db[id].lits.empty())empty=true;
  }
  // Returns true only after finding a falsified antecedent. Every earlier
  // antecedent must be unit; assignments are recorded for later restoration.
  bool propagate(const vector<long long>&hs,size_t begin,size_t end){
    for(size_t i=begin;i<end;i++){
      if(hs[i]<=0||hs[i]>2147483647)throw runtime_error("bad RUP hint");
      const auto &c=get(int(hs[i]));int unit=0;bool sat=false;
      for(int l:c){int v=value(l);if(v>0){sat=true;break;}if(v==0){if(unit&&unit!=l)throw runtime_error("hint is not unit");unit=l;}}
      if(sat)throw runtime_error("satisfied RUP hint");
      if(!unit)return true;
      if(!set(unit))return true;
    }
    return false;
  }
  void verify(int id,vector<int> c,const vector<long long>&hs){
    undo(0);bool taut=false;for(int l:c)if(!set(-l)){taut=true;break;}
    for(auto h:hs)if(h<=0)throw runtime_error("RAT steps are not supported");
    if(!taut&&!propagate(hs,0,hs.size()))throw runtime_error("RUP did not derive conflict");
    ++rup;undo(0);add(id,move(c));
  }
};
int main(int argc,char**argv){try{
  if(argc!=3)throw runtime_error("usage: check_lrat input.cnf proof.lrat");auto start=chrono::steady_clock::now();
  ifstream input(argv[1]);if(!input)throw runtime_error("cannot open CNF");string line;Checker k;int nv=0,nc=0;
  while(getline(input,line)){if(line.empty()||line[0]=='c')continue;istringstream s(line);string p,cnf;s>>p>>cnf>>nv>>nc;if(p!="p"||cnf!="cnf"||nv<0||nc<0)throw runtime_error("bad CNF header");break;}
  k.val.resize(nv+1);vector<int> c;int l,id=0;
  while(input>>l){if(l)c.push_back(l);else{k.add(++id,move(c));c.clear();}}
  if(id!=nc||!c.empty())throw runtime_error("CNF count mismatch");
  ifstream proof(argv[2]);if(!proof)throw runtime_error("cannot open proof");long long lines=0;
  while(getline(proof,line)){
    ++lines;if(line.empty()||line[0]=='c')continue;istringstream s(line);int newid;string token;if(!(s>>newid>>token))throw runtime_error("bad proof line");
    if(token=="d") {bool end=false;while(s>>l){if(!l){end=true;break;}if(l<=0||size_t(l)>=k.db.size())throw runtime_error("bad deletion");k.db[l].live=false;++k.del;}if(!end)throw runtime_error("unterminated deletion");}
    else {c.clear();l=stoi(token);while(l){c.push_back(l);if(!(s>>l))throw runtime_error("unterminated clause");}
      vector<long long> hs;long long h;bool end=false;while(s>>h){if(!h){end=true;break;}hs.push_back(h);}if(!end)throw runtime_error("unterminated hints");k.verify(newid,move(c),hs);
    }
    if(lines%100000==0)cerr<<"checked "<<lines<<" proof lines\n";
  }
  if(!k.empty)throw runtime_error("no empty clause derived");
  cout<<"VERIFIED UNSAT; RUP="<<k.rup<<" RAT=0 deleted="<<k.del<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
  return 0;
}catch(const exception&e){cerr<<"REJECTED: "<<e.what()<<"\n";return 1;}}
