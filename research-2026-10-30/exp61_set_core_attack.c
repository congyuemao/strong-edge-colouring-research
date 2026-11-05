/* exp61: adversary against "some colour set Y, |Y| = k, has h outside the core C_Y" (NEW_DIRECTIONS 11.26).
   S_Y = edges not coloured from Y at which every pair of Y is tangled.  tau_Y(v) = 2(20-k) - deg(v) + d_Y(v).  Peel; v(Y) = 0 if h stays, else GW + 1 + edges peeled when h goes
   (GW + 1 + m if h is not in S_Y).  Energy = 100000 * #colours missing at h + sum v(Y).  Zero: counterexample at this k.
   Moves: Kempe swap of one component at a random edge of the region; parallel tempering in one thread.  Input as exp57: m h nr / colours / region / adjacency.
   Usage: exp61 k input output seconds seed */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define K 20
#define MAXM 800
#define WMAX (MAXM/64+1)
#define MAXY 4845
static int m,h,W,GW,KY;
static uint64_t adj[MAXM][WMAX]; static int nb[MAXM][32], nd[MAXM];
static int region[MAXM], nr;
static int ny; static int ysets[MAXY][4]; static int ymask[MAXY];
typedef struct { int col[MAXM]; uint64_t cls[K][WMAX]; uint64_t tang[K][K][WMAX]; int val[MAXY]; int miss; long sep; double T; } St;
static uint64_t rs;
static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline int bit(const uint64_t*a,int i){return a[i>>6]>>(i&63)&1;}
static void tangle(St*s,int a,int b){
  static int comp[MAXM], st[MAXM];
  uint64_t U[WMAX],vis[WMAX]; for(int i=0;i<W;i++){U[i]=s->cls[a][i]|s->cls[b][i];vis[i]=0;}
  for(int i=0;i<W;i++){uint64_t v=U[i];while(v){int t=__builtin_ctzll(v);v&=v-1;if(vis[i]>>t&1)continue;int x=64*i+t,sp=0;st[sp++]=x;vis[i]|=1ULL<<t;comp[x]=x;
    while(sp){int y=st[--sp];for(int j=0;j<nd[y];j++){int z=nb[y][j];if(bit(U,z)&&!bit(vis,z)){vis[z>>6]|=1ULL<<(z&63);comp[z]=x;st[sp++]=z;}}}}}
  uint64_t*T=s->tang[a][b]; memset(T,0,sizeof(uint64_t)*W);
  for(int v=0;v<m;v++){ if(bit(U,v))continue; int ca[32],na=0,hit=0;
    for(int j=0;j<nd[v];j++){int z=nb[v][j]; if(bit(s->cls[a],z))ca[na++]=comp[z];}
    if(!na)continue;
    for(int j=0;j<nd[v]&&!hit;j++){int z=nb[v][j]; if(bit(s->cls[b],z))for(int q=0;q<na;q++)if(ca[q]==comp[z]){hit=1;break;}}
    if(hit)T[v>>6]|=1ULL<<(v&63);
  }
}
static int evalY(St*s,int y){
  static int st[MAXM],tau[MAXM],cnt[MAXM]; static uint8_t inS[MAXM],qd[MAXM];
  const int*Y=ysets[y]; uint64_t S[WMAX],C[WMAX];
  for(int i=0;i<W;i++){S[i]=~0ULL;C[i]=0;}
  for(int p=0;p<KY;p++){for(int i=0;i<W;i++)C[i]|=s->cls[Y[p]][i]; for(int q=p+1;q<KY;q++){const uint64_t*T=s->tang[Y[p]][Y[q]];for(int i=0;i<W;i++)S[i]&=T[i];}}
  if(!bit(S,h))return GW+1+m;
  int ns=0;
  for(int v=0;v<m;v++){inS[v]=bit(S,v); ns+=inS[v];}
  int qh=0,qt=0,rem=m-ns; 
  for(int v=0;v<m;v++)if(inS[v]){int c=0,d=0;for(int j=0;j<nd[v];j++){int z=nb[v][j];c+=inS[z];d+=bit(C,z);} cnt[v]=c;tau[v]=2*(K-KY)-nd[v]+d; qd[v]=0; if(c<tau[v]){st[qt++]=v;qd[v]=1;}}
  while(qh<qt){int v=st[qh++];inS[v]=0;rem++;if(v==h)return GW+1+rem;for(int j=0;j<nd[v];j++){int z=nb[v][j];if(inS[z]&&!qd[z]&&--cnt[z]<tau[z]){qd[z]=1;st[qt++]=z;}else if(inS[z]&&qd[z])--cnt[z];}}
  return 0;
}
static void recompute(St*s,int p,int q,int full){
  s->miss=0; for(int c=0;c<K;c++){int any=0;for(int i=0;i<W;i++)if(s->cls[c][i]&adj[h][i])any=1; if(!any)s->miss++;}
  for(int a=0;a<K;a++)for(int b=a+1;b<K;b++){ if(!full&&a!=p&&a!=q&&b!=p&&b!=q)continue; tangle(s,a,b);}
  int mask=full?-1:(1<<p)|(1<<q);
  for(int y=0;y<ny;y++) if(ymask[y]&mask){int v=evalY(s,y); s->sep+=v-s->val[y]; s->val[y]=v;}
}
static inline long energy(St*s){return 100000L*s->miss+s->sep;}
static void component(St*s,int x,int p,int q,int*c,int*n){ uint64_t U[WMAX],vis[WMAX]; for(int i=0;i<W;i++){U[i]=s->cls[p][i]|s->cls[q][i];vis[i]=0;} int sp=0,cnt=0; c[cnt++]=x; vis[x>>6]|=1ULL<<(x&63); while(sp<cnt){int y=c[sp++]; for(int j=0;j<nd[y];j++){int z=nb[y][j]; if(bit(U,z)&&!bit(vis,z)){vis[z>>6]|=1ULL<<(z&63);c[cnt++]=z;}}} *n=cnt; }
static void doswap(St*s,int*c,int n,int p,int q){ for(int i=0;i<n;i++){int x=c[i]; int o=s->col[x],w=(o==p)?q:p; s->cls[o][x>>6]&=~(1ULL<<(x&63)); s->cls[w][x>>6]|=1ULL<<(x&63); s->col[x]=w;} }
int main(int ac,char**av){
  KY=atoi(av[1]); FILE*f=fopen(av[2],"r"); if(fscanf(f,"%d %d %d",&m,&h,&nr)!=3)return 1; W=(m+63)/64; GW=m;
  int col0[MAXM]; for(int i=0;i<m;i++)if(fscanf(f,"%d",&col0[i])!=1)return 1;
  for(int i=0;i<nr;i++)if(fscanf(f,"%d",&region[i])!=1)return 1;
  for(int i=0;i<m;i++){ if(fscanf(f,"%d",&nd[i])!=1)return 1; for(int j=0;j<nd[i];j++){int y; if(fscanf(f,"%d",&y)!=1)return 1; nb[i][j]=y; adj[i][y>>6]|=1ULL<<(y&63);} }
  fclose(f);
  ny=0; for(int s=0;s<(1<<K);s++) if(__builtin_popcount(s)==KY){int t=0;for(int c=0;c<K;c++)if(s>>c&1)ysets[ny][t++]=c; ymask[ny]=s; ny++;}
  double secs=atof(av[4]); rs=strtoull(av[5],0,10)*0x9E3779B97F4A7C15ULL+1;
  enum{RUNGS=8}; St*st=calloc(RUNGS,sizeof(St)); St*best=malloc(sizeof(St)); long bestE=1L<<60; int order[RUNGS]; for(int r=0;r<RUNGS;r++)order[r]=r;
  for(int r=0;r<RUNGS;r++){St*s=&st[r]; for(int i=0;i<m;i++){s->col[i]=col0[i]; if(i!=h&&col0[i]>=0)s->cls[col0[i]][i>>6]|=1ULL<<(i&63);} s->col[h]=-1; recompute(s,0,0,1); s->T=1.0*pow(300.0,(double)r/(RUNGS-1));}
  time_t t0=time(0),tl=t0; long steps=0; *best=st[0]; bestE=energy(&st[0]);
  int good0=0; for(int y=0;y<ny;y++)good0+=st[0].val[y]>0;
  fprintf(stderr,"start energy %ld miss %d good %d/%d\n",energy(&st[0]),st[0].miss,good0,ny);
  while(difftime(time(0),t0)<secs){
    for(int r=0;r<RUNGS;r++){St*s=&st[r];
      for(int it=0;it<10;it++){
        int x=region[rnd()%nr]; int p=s->col[x]; if(p<0)continue; int q=rnd()%K; if(q==p)continue;
        int c[MAXM],n; component(s,x,p,q,c,&n); long E0=energy(s);
        doswap(s,c,n,p,q); recompute(s,p,q,0); long E1=energy(s); steps++;
        if(E1<=E0||(double)(rnd()>>11)/9007199254740992.0<exp((E0-E1)/s->T)){ if(E1<bestE){bestE=E1;*best=*s; if(E1==0)goto done;} }
        else { doswap(s,c,n,p,q); recompute(s,p,q,0);}
      }
    }
    for(int r=0;r+1<RUNGS;r++){St*A=&st[r],*B=&st[r+1]; double d=(1/A->T-1/B->T)*(energy(A)-energy(B)); if(d>=0||(double)(rnd()>>11)/9007199254740992.0<exp(d)){double t=A->T;A->T=B->T;B->T=t;}}
    if(difftime(time(0),tl)>=120){tl=time(0);int g=0;for(int y=0;y<ny;y++)g+=best->val[y]>0;fprintf(stderr,"[%.0f s] steps %ld best %ld good %d/%d miss %d\n",difftime(tl,t0),steps,bestE,g,ny,best->miss);FILE*o=fopen(av[3],"w");fprintf(o,"%ld\n",bestE);for(int i=0;i<m;i++)fprintf(o,"%d ",best->col[i]);fclose(o);}
  }
  done:;
  {int g=0;for(int y=0;y<ny;y++)g+=best->val[y]>0;FILE*o=fopen(av[3],"w");fprintf(o,"%ld\n",bestE);for(int i=0;i<m;i++)fprintf(o,"%d ",best->col[i]);fclose(o);
  fprintf(stderr,"end steps %ld best %ld good %d/%d miss %d\n",steps,bestE,g,ny,best->miss);}
  return 0;
}
