/* exp57 (from exp53): adversary against "some colour pair has the two-colour core missing h" (NEW_DIRECTIONS 11.25). Old header: (NEW_DIRECTIONS 11.24).
   State: proper 20-colouring of L^2 - h.  Energy = 200*(#colours missing from N(h)) + #separable pairs + #triples Y with h peeled
   from U_Y at threshold 3.  Energy 0: h blocked, no separable pair, no peeling repair with |Y| = 3.
   Moves: Kempe swap of one component at a random edge within L^2-distance R of h; a single-edge component is a recolouring.
   Parallel tempering between ladder rungs in one thread.  A move touches colours p, q; only the triples and pairs containing p
   or q are recomputed.  Input file: m h R / colours / adjacency lists.  Usage: exp53 input output seconds seed */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define K 20
#define MAXM 1600
#define WMAX (MAXM/64)
static int m,h,W;
static uint64_t adj[MAXM][WMAX]; static int nb[MAXM][32], nd[MAXM];
static int region[MAXM], nr;
typedef struct { int col[MAXM]; uint64_t cls[K][WMAX]; int pairsep[K][K]; uint8_t triple[K][K][K]; int miss, sep, tri; double T; } St;
static uint64_t rs;
static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static int popc(const uint64_t*a,const uint64_t*b){int s=0;for(int i=0;i<W;i++)s+=__builtin_popcountll(a[i]&b[i]);return s;}
static int goodpair(St*s,int a,int b){
  /* 1 if h is outside the core C_ab: separable at h, or peeled from S_ab with threshold tau(v) = 12 + d_ab(v) */
  static __thread int comp[MAXM], st[MAXM], tau[MAXM], cnt[MAXM]; static __thread uint8_t inS[MAXM];
  uint64_t U[WMAX],vis[WMAX]; for(int i=0;i<W;i++){U[i]=s->cls[a][i]|s->cls[b][i];vis[i]=0;}
  for(int i=0;i<W;i++){uint64_t v=U[i];while(v){int t=__builtin_ctzll(v);v&=v-1;int x=64*i+t; if(vis[i]>>t&1)continue; int sp=0; st[sp++]=x; vis[i]|=1ULL<<t; comp[x]=x;
    while(sp){int y=st[--sp]; for(int j=0;j<nd[y];j++){int z=nb[y][j]; if((U[z>>6]>>(z&63)&1)&&!(vis[z>>6]>>(z&63)&1)){vis[z>>6]|=1ULL<<(z&63);comp[z]=x;st[sp++]=z;}}}}}
  int ns=0;
  for(int v=0;v<m;v++){ inS[v]=0; if(U[v>>6]>>(v&63)&1)continue;
    int ca[32],na=0,d=0,hit=0;
    for(int j=0;j<nd[v];j++){int z=nb[v][j]; if(z==h)continue; if(s->cls[a][z>>6]>>(z&63)&1){ca[na++]=comp[z];d++;}}
    for(int j=0;j<nd[v];j++){int z=nb[v][j]; if(z==h)continue; if(s->cls[b][z>>6]>>(z&63)&1){d++; for(int q=0;q<na;q++) if(ca[q]==comp[z])hit=1;}}
    tau[v]=36-nd[v]+d; if(hit){inS[v]=1;ns++;}
  }
  /* graded value: 0 if h stays in the core, else 1 + (edges already peeled when h goes, in FIFO order); smaller = closer to a core */
  if(!inS[h])return 1+m;
  int qh=0,qt=0,rem=m-ns;
  for(int v=0;v<m;v++) if(inS[v]){int c=0; for(int j=0;j<nd[v];j++) c+=inS[nb[v][j]]; cnt[v]=c; if(c<tau[v])st[qt++]=v;}
  static __thread uint8_t qd[MAXM]; memset(qd,0,m); for(int i=0;i<qt;i++)qd[st[i]]=1;
  while(qh<qt){int v=st[qh++]; inS[v]=0; rem++; if(v==h)return 1+rem; for(int j=0;j<nd[v];j++){int z=nb[v][j]; if(inS[z]&&!qd[z]&&--cnt[z]<tau[z]){qd[z]=1;st[qt++]=z;}}}
  return 0;
}
static void recompute(St*s,int p,int q,int full){
  s->miss=0; for(int c=0;c<K;c++){int any=0;for(int i=0;i<W;i++)if(s->cls[c][i]&adj[h][i])any=1; if(!any)s->miss++;}
  for(int a=0;a<K;a++)for(int b=a+1;b<K;b++){ if(!full&&a!=p&&a!=q&&b!=p&&b!=q)continue;
    int v=goodpair(s,a,b); if(v!=s->pairsep[a][b]){s->sep+=v-s->pairsep[a][b];s->pairsep[a][b]=v;} }
}
static inline int energy(St*s){return 100000*s->miss+s->sep;}
static void component(St*s,int x,int a,int b,int*out,int*n){
  uint64_t U[WMAX],vis[WMAX]; for(int i=0;i<W;i++){U[i]=s->cls[a][i]|s->cls[b][i];vis[i]=0;}
  *n=0; int st[MAXM],sp=0; st[sp++]=x; vis[x>>6]|=1ULL<<(x&63);
  while(sp){int y=st[--sp]; out[(*n)++]=y; for(int i=0;i<W;i++){uint64_t nw=adj[y][i]&U[i]&~vis[i]; vis[i]|=nw; while(nw){int t=__builtin_ctzll(nw);nw&=nw-1;st[sp++]=64*i+t;}}}
}
static void doswap(St*s,int*c,int n,int a,int b){
  for(int i=0;i<n;i++){int x=c[i]; int o=s->col[x], w=(o==a)?b:a; s->col[x]=w; s->cls[o][x>>6]&=~(1ULL<<(x&63)); s->cls[w][x>>6]|=1ULL<<(x&63);}
}
int main(int ac,char**av){
  FILE*f=fopen(av[1],"r"); int R; if(fscanf(f,"%d %d %d",&m,&h,&nr)!=3)return 1; W=(m+63)/64;
  int col0[MAXM]; for(int i=0;i<m;i++)if(fscanf(f,"%d",&col0[i])!=1)return 1;
  for(int i=0;i<nr;i++)if(fscanf(f,"%d",&region[i])!=1)return 1;
  for(int i=0;i<m;i++){ if(fscanf(f,"%d",&nd[i])!=1)return 1; for(int j=0;j<nd[i];j++){int y; if(fscanf(f,"%d",&y)!=1)return 1; nb[i][j]=y; adj[i][y>>6]|=1ULL<<(y&63);} }
  fclose(f); (void)R;
  double secs=atof(av[3]); rs=strtoull(av[4],0,10)*0x9E3779B97F4A7C15ULL+1;
  enum{RUNGS=12}; static St st[RUNGS], best; int bestE=1<<30;
  for(int r=0;r<RUNGS;r++){St*s=&st[r]; memset(s,0,sizeof(*s)); for(int i=0;i<m;i++){s->col[i]=col0[i]; if(i!=h&&col0[i]>=0)s->cls[col0[i]][i>>6]|=1ULL<<(i&63);} s->col[h]=-1; recompute(s,0,0,1); s->T=1.0*pow(100.0,(double)r/(RUNGS-1));}
  time_t t0=time(0),tl=t0; long steps=0;
  fprintf(stderr,"start energy %d sep %d tri %d miss %d\n",energy(&st[0]),st[0].sep,st[0].tri,st[0].miss);
  while(difftime(time(0),t0)<secs){
    for(int r=0;r<RUNGS;r++){St*s=&st[r];
      for(int it=0;it<20;it++){
        int x=region[rnd()%nr]; int p=s->col[x]; if(p<0)continue; int q=rnd()%K; if(q==p)continue;
        int c[MAXM],n; component(s,x,p,q,c,&n); int E0=energy(s);
        doswap(s,c,n,p,q); recompute(s,p,q,0); int E1=energy(s); steps++;
        if(E1<=E0||(double)(rnd()>>11)/9007199254740992.0<exp((E0-E1)/s->T)){ if(E1<bestE){bestE=E1;best=*s; if(E1==0)goto done;} }
        else { doswap(s,c,n,p,q); recompute(s,p,q,0);} 
      }
    }
    for(int r=0;r+1<RUNGS;r++){double d=(1/st[r].T-1/st[r+1].T)*(energy(&st[r])-energy(&st[r+1])); if(d>=0||(double)(rnd()>>11)/9007199254740992.0<exp(d)){double t=st[r].T;st[r].T=st[r+1].T;st[r+1].T=t;St tmp=st[r];st[r]=st[r+1];st[r+1]=tmp;}}
    if(difftime(time(0),tl)>=120){tl=time(0);fprintf(stderr,"[%.0f s] steps %ld best %d (sep %d tri %d miss %d)\n",difftime(tl,t0),steps,bestE,best.sep,best.tri,best.miss);FILE*o=fopen(av[2],"w");fprintf(o,"%d\n",bestE);for(int i=0;i<m;i++)fprintf(o,"%d ",best.col[i]);fclose(o);}
  }
  done:;
  FILE*o=fopen(av[2],"w");fprintf(o,"%d\n",bestE);for(int i=0;i<m;i++)fprintf(o,"%d ",best.col[i]);fclose(o);
  fprintf(stderr,"end steps %ld best %d (sep %d tri %d miss %d)\n",steps,bestE,best.sep,best.tri,best.miss);
  return 0;
}
