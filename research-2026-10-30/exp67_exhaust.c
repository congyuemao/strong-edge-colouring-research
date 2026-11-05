/* exp67: exhaustive check of the colour-set core conjectures on small graphs (NEW_DIRECTIONS 11.27).
   Input as exp61 (m h nr / colours / region / adjacency; colours and region ignored).
   Enumerates every proper K-colouring of L^2 - h up to renaming colours.  For each with all K colours at h and no separable pair at h (one-step stuck),
   records for k = 2..K-1 the number of colour sets with h outside the core.  Prints the minimum over states of the number of good sets, the number of stuck
   states, and the minimum of the one-layer sum; writes the worst state for k = 2.
   Usage: exp67 k_max input [state_limit]  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#ifndef K
#define K 10
#endif
#define MAXM 64
static int m,h,nd[MAXM],nb[MAXM][32],order[MAXM],col[MAXM];
static long long states=0,stuck=0,limit=0; static int kmax;
static long minGood[K+1],minSum=1L<<30,maxFail[K+1]; static long allFail[K+1];
static int worst[MAXM];
static uint64_t tang[K][K];
static inline void tangle(int a,int b){
  int comp[MAXM]; for(int i=0;i<m;i++)comp[i]=-1;
  for(int s=0;s<m;s++) if((col[s]==a||col[s]==b)&&comp[s]<0){int st[MAXM],sp=0;st[sp++]=s;comp[s]=s;while(sp){int u=st[--sp];for(int j=0;j<nd[u];j++){int w=nb[u][j];if((col[w]==a||col[w]==b)&&comp[w]<0){comp[w]=s;st[sp++]=w;}}}}
  uint64_t T=0;
  for(int v=0;v<m;v++){ if(col[v]==a||col[v]==b)continue; uint64_t A=0; for(int j=0;j<nd[v];j++){int z=nb[v][j]; if(col[z]==a)A|=1ULL<<comp[z];}
    if(!A)continue; int hit=0; for(int j=0;j<nd[v];j++){int z=nb[v][j]; if(col[z]==b&&(A>>comp[z]&1))hit=1;} if(hit)T|=1ULL<<v;}
  tang[a][b]=T;
}
static inline int corehasH(int mask,int k){
  uint64_t S=~0ULL,C=0; int ys[K],n=0; for(int c=0;c<K;c++)if(mask>>c&1)ys[n++]=c;
  for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)S&=tang[ys[i]][ys[j]];
  for(int v=0;v<m;v++)if(col[v]>=0&&(mask>>col[v]&1))S&=~(1ULL<<v);
  if(!(S>>h&1))return 0;
  int ch=1; while(ch){ch=0; for(int v=0;v<m;v++)if(S>>v&1){int c=0,d=0;for(int j=0;j<nd[v];j++){int z=nb[v][j];c+=S>>z&1; d+=(col[z]>=0&&(mask>>col[z]&1));} if(c<2*(K-k)-nd[v]+d){S&=~(1ULL<<v);ch=1; if(v==h)return 0;}}}
  return S>>h&1;
}
static void leaf(void){
  states++;
  int seen=0; for(int j=0;j<nd[h];j++)seen|=1<<col[nb[h][j]];
  if(seen!=(1<<K)-1)return;
  for(int a=0;a<K;a++)for(int b=a+1;b<K;b++){tangle(a,b); if(!(tang[a][b]>>h&1))return;}
  stuck++;
  long sum=0; for(int a=0;a<K;a++)for(int b=a+1;b<K;b++)for(int j=0;j<nd[h];j++){int z=nb[h][j]; if(col[z]!=a&&col[z]!=b&&!(tang[a][b]>>z&1))sum++;}
  if(sum<minSum)minSum=sum;
  for(int k=2;k<=kmax;k++){ long good=0,tot=0; for(int s=0;s<(1<<K);s++)if(__builtin_popcount(s)==k){tot++; if(!corehasH(s,k))good++;}
    if(good<minGood[k]){minGood[k]=good; if(k==2)memcpy(worst,col,sizeof(col));}
    if(good==0)allFail[k]++; }
}
static void dfs(int i,int used){
  if(limit&&states>=limit)return;
  if(i==m-1){leaf();return;}
  if(i==nd[h]){int seen=0; for(int j=0;j<nd[h];j++)seen|=1<<col[nb[h][j]]; if(seen!=(1<<K)-1)return;}
  int v=order[i]; int forb=0; for(int j=0;j<nd[v];j++){int z=nb[v][j]; if(col[z]>=0)forb|=1<<col[z];}
  int top=used<K?used+1:K;
  for(int c=0;c<top;c++) if(!(forb>>c&1)){col[v]=c; dfs(i+1,c==used?used+1:used); col[v]=-1;}
}
int main(int ac,char**av){
  kmax=atoi(av[1]); FILE*f=fopen(av[2],"r"); int nr; if(fscanf(f,"%d %d %d",&m,&h,&nr)!=3)return 1; int x; for(int i=0;i<m+nr;i++)if(fscanf(f,"%d",&x)!=1)return 1;
  for(int i=0;i<m;i++){if(fscanf(f,"%d",&nd[i])!=1)return 1; for(int j=0;j<nd[i];j++)if(fscanf(f,"%d",&nb[i][j])!=1)return 1;} fclose(f);
  if(ac>3)limit=atoll(av[3]);
  for(int k=0;k<=K;k++)minGood[k]=1L<<30;
  /* order: neighbours of h first, then greedily most constrained */
  int done[MAXM]={0}; done[h]=1; int n=0;
  for(int j=0;j<nd[h];j++){order[n++]=nb[h][j];done[nb[h][j]]=1;}
  while(n<m-1){int b=-1,bs=-1;for(int v=0;v<m;v++)if(!done[v]){int s=0;for(int j=0;j<nd[v];j++)s+=done[nb[v][j]]; if(s>bs){bs=s;b=v;}} order[n++]=b;done[b]=1;}
  for(int i=0;i<m;i++)col[i]=-1;
  dfs(0,0);
  printf("m=%d deg_h=%d colourings=%lld%s stuck=%lld minSum=%ld (threshold %d)",m,nd[h],states,(limit&&states>=limit)?"(LIMIT)":"",stuck,minSum==1L<<30?-1:minSum,nd[h]*(K-1)*(K-2)/2/3);
  for(int k=2;k<=kmax;k++)if(stuck)printf(" k%d:minGood=%ld,allFail=%ld",k,minGood[k],allFail[k]);
  printf("\n"); return 0;
}
