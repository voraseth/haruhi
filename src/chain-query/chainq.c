/* chainq.c -- endpoint-pinned hop-chain EXISTENCE queries (T-n6-highe).
 * Adapted from the registered enumerator approaches/n6-871/checks/chains871.c
 * (raw definitions of proof6.md sections 1,3,7).
 *
 * Query (one per stdin line):  c s5 s4 lf lb B
 *   does a hop-chain exist with cost EXACTLY c, EXACTLY s5 length-4 paths,
 *   EXACTLY s4 length<=3 paths, first-path length lf (1..5, or 0 = free),
 *   last-path length lb (1..5, or 0 = free), and at least B blocks?
 * WLOG the head crit is 123456 (relabelling is transitive and commutes with
 * rot, rho, sig, d).  Output per line: YES/NO + nodes.  Exhaustive DFS with
 * sound prunes only (C6-A run caps; cost-composition window).            */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static unsigned char P[720][6];
static int ROT[720], RHO[720], CLS[720];
static signed char DIST[720][720];
static int idx_of[46656];
static int code(const unsigned char*a){int c=0;for(int i=0;i<6;i++)c=c*6+(a[i]-1);return c;}
static void build(void){
  int n=0; unsigned char a[6];
  for(a[0]=1;a[0]<=6;a[0]++)for(a[1]=1;a[1]<=6;a[1]++){if(a[1]==a[0])continue;
   for(a[2]=1;a[2]<=6;a[2]++){if(a[2]==a[0]||a[2]==a[1])continue;
    for(a[3]=1;a[3]<=6;a[3]++){if(a[3]==a[0]||a[3]==a[1]||a[3]==a[2])continue;
     for(a[4]=1;a[4]<=6;a[4]++){if(a[4]==a[0]||a[4]==a[1]||a[4]==a[2]||a[4]==a[3])continue;
      for(a[5]=1;a[5]<=6;a[5]++){int ok=1;for(int i=0;i<5;i++)if(a[5]==a[i])ok=0;if(!ok)continue;
       memcpy(P[n],a,6); n++;}}}}}
  if(n!=720){fprintf(stderr,"perm build failed\n");exit(1);}
  for(int i=0;i<46656;i++)idx_of[i]=-1;
  for(int i=0;i<720;i++) idx_of[code(P[i])]=i;
  unsigned char t[6];
  for(int i=0;i<720;i++){
    for(int k=0;k<5;k++)t[k]=P[i][k+1]; t[5]=P[i][0]; ROT[i]=idx_of[code(t)];
    t[0]=P[i][1];t[1]=P[i][2];t[2]=P[i][3];t[3]=P[i][4];t[4]=P[i][0];t[5]=P[i][5];
    RHO[i]=idx_of[code(t)];
  }
  for(int i=0;i<720;i++){int m=i,c=i;for(int k=0;k<5;k++){c=ROT[c];if(c<m)m=c;}CLS[i]=m;}
  for(int i=0;i<720;i++)for(int j=0;j<720;j++){
    int dd=6;
    for(int k=1;k<=5;k++){int ok=1;for(int t2=0;t2<6-k;t2++)if(P[i][k+t2]!=P[j][t2]){ok=0;break;}
      if(ok){dd=k;break;}}
    DIST[i][j]=(signed char)dd;
  }
}
static int used[720];
static long long NODES;
static int QC,QS5,QS4,QLF,QLB,QB;   /* the query */
static int NB,COST,NS5,NS4,FOUND,LASTL;
static int seg_ok(int x,int l,int *cl){
  int y=x;
  for(int j=0;j<l;j++){ cl[j]=CLS[y]; if(used[cl[j]]) return 0;
    for(int t=0;t<j;t++) if(cl[t]==cl[j]) return 0;
    y=RHO[y]; }
  return 1;
}
static int seg_end(int x,int l){ int y=x; for(int j=0;j<l-1;j++)y=RHO[y];
  for(int k=0;k<5;k++)y=ROT[y]; return y; }
static void dfs(int x,int runlen){
  if(FOUND) return;
  NODES++;
  int cl[5];
  for(int l=1;l<=5;l++){
    if(FOUND) return;
    int c=5-l;
    if(NB==0 && QLF && l!=QLF) continue;
    if(COST+c>QC) continue;
    int ns5=NS5+(l==4), ns4=NS4+(l<4);
    if(ns5>QS5 || ns4>QS4) continue;
    int nrl=(l>=4)?runlen+1:0;
    if(nrl>4) continue;                              /* C6-A run cap */
    if(!seg_ok(x,l,cl)) continue;
    for(int j=0;j<l;j++) used[cl[j]]=1;
    NB++; COST+=c; NS5=ns5; NS4=ns4;
    /* remaining composition window */
    int r5=QS5-NS5, r4=QS4-NS4, rm=QC-COST;
    if(rm>=r5+2*r4 && rm<=r5+4*r4){
      if(NB>=QB && COST==QC && NS5==QS5 && NS4==QS4 &&
         (QLB==0 || l==QLB)) FOUND=1;
      if(!FOUND){
        /* sound block bound: rest of current run + 4 blocks per >=cost-2 break */
        /* every future {4,5}-run needs a distinct remaining short separator,
           so additional blocks <= (rest of current run) + r4 shorts + 4*r4 */
        int ub=NB+(4-((l>=4)?nrl:0))+5*r4;
        if(ub>=QB){
          int e=seg_end(x,l);
          for(int nx=0;nx<720 && !FOUND;nx++) if(DIST[e][nx]==3) dfs(nx,nrl);
        }
      }
    }
    NB--; COST-=c; NS5-=(l==4); NS4-=(l<4);
    for(int j=0;j<l;j++) used[cl[j]]=0;
  }
}
int main(void){
  build();
  char line[256];
  while(fgets(line,sizeof line,stdin)){
    if(sscanf(line,"%d %d %d %d %d %d",&QC,&QS5,&QS4,&QLF,&QLB,&QB)!=6) continue;
    memset(used,0,sizeof used);
    NB=0;COST=0;NS5=0;NS4=0;FOUND=0;NODES=0;
    dfs(0,0);
    printf("Q c=%d s5=%d s4=%d lf=%d lb=%d B=%d : %s nodes=%lld\n",
           QC,QS5,QS4,QLF,QLB,QB,FOUND?"YES":"NO",NODES);
    fflush(stdout);
  }
  return 0;
}
