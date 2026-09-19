/* cover.c -- JOINT class-cover certifier (T-n6-highe).
 * Enumerates EXHAUSTIVELY the non-cycle chains of a surviving profile
 * decomposition (chain 1 head fixed 123456 WLOG; chain 2, if any, from every
 * head) and, for each completed chain configuration, checks the NECESSARY
 * condition that the leftover classes partition into rho-4-segments
 * {C(x),C(rho x),C(rho^2 x),C(rho^3 x)} -- the class sets of the T1 cycles
 * forced by CYC5-n6 (all cycles are T1 in these profiles: c2=0 forced).
 * If no configuration passes, the profile is EMPTY.
 * usage: cover NQ  c1 s51 s41 lf1 lb1 B1  [c2 s52 s42 lf2 lb2 B2]
 *   NQ = number of rho-4-segments the leftover must split into.       */
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
static int used[720];               /* class-id -> used by a chain */
static long long NODES, CONFIGS, COVERS, C1DONE;
static int NQ;
static int Q[2][6];                 /* per-chain spec c s5 s4 lf lb B */
/* ---- leftover cover check ---- */
static int leftover[120], NL;
static int qcand[3000][4], NC_;
static int covered[720];
static int cover_dfs(int nleft){
  if(nleft==0) return 1;
  int pick=-1;
  for(int i=0;i<NL;i++) if(!covered[leftover[i]]){pick=leftover[i];break;}
  for(int q=0;q<NC_;q++){
    int hit=0,ok=1;
    for(int j=0;j<4;j++){int c=qcand[q][j];
      if(covered[c]){ok=0;break;} if(c==pick)hit=1;}
    if(!ok||!hit) continue;
    for(int j=0;j<4;j++) covered[qcand[q][j]]=1;
    if(cover_dfs(nleft-4)) return 1;
    for(int j=0;j<4;j++) covered[qcand[q][j]]=0;
  }
  return 0;
}
static int check_cover(void){
  NL=0;
  for(int i=0;i<720;i++) if(CLS[i]==i && !used[i]) leftover[NL++]=i;
  if(NL != 4*NQ) return 0;
  /* candidate quads inside leftover */
  NC_=0;
  for(int x=0;x<720;x++){
    int y=x, cl[4], ok=1;
    for(int j=0;j<4;j++){ cl[j]=CLS[y]; if(used[cl[j]]){ok=0;break;} y=RHO[y]; }
    if(!ok) continue;
    for(int j=0;j<4&&ok;j++)for(int t=0;t<j;t++)if(cl[t]==cl[j])ok=0;
    if(!ok) continue;
    /* dedupe by sorted quad */
    int s[4]; memcpy(s,cl,sizeof s);
    for(int a=0;a<3;a++)for(int b=a+1;b<4;b++)if(s[b]<s[a]){int t=s[a];s[a]=s[b];s[b]=t;}
    int dup=0;
    for(int q=0;q<NC_;q++) if(!memcmp(qcand[q],s,sizeof s)){dup=1;break;}
    if(!dup){ memcpy(qcand[NC_],s,sizeof s); NC_++; }
  }
  memset(covered,0,sizeof covered);
  return cover_dfs(NL);
}
/* ---- chain DFS ---- */
static int NB,COST,NS5,NS4;
static int seg_ok(int x,int l,int *cl){
  int y=x;
  for(int j=0;j<l;j++){ cl[j]=CLS[y]; if(used[cl[j]]) return 0;
    for(int t=0;t<j;t++) if(cl[t]==cl[j]) return 0;
    y=RHO[y]; }
  return 1;
}
static int seg_end(int x,int l){ int y=x; for(int j=0;j<l-1;j++)y=RHO[y];
  for(int k=0;k<5;k++)y=ROT[y]; return y; }
static void chain_dfs(int ci, int nchains, int x, int runlen);
static void chain_done(int ci,int nchains){
  if(ci==0) C1DONE++;
  CONFIGS += (ci==nchains-1);
  if(ci==nchains-1){
    if(check_cover()){
      COVERS++;
      if(COVERS<=3) printf("COVER FOUND (config %lld)\n",CONFIGS);
    }
  } else {
    /* next chain: every head */
    for(int nx=0;nx<720;nx++) chain_dfs(ci+1,nchains,nx,0);
  }
}
static void chain_dfs(int ci,int nchains,int x,int runlen){
  NODES++;
  int c0=Q[ci][0],s50=Q[ci][1],s40=Q[ci][2],lf=Q[ci][3],lb=Q[ci][4],B=Q[ci][5];
  int cl[5];
  for(int l=1;l<=5;l++){
    int c=5-l;
    if(NB==0 && lf && l!=lf) continue;
    if(COST+c>c0) continue;
    int ns5=NS5+(l==4), ns4=NS4+(l<4);
    if(ns5>s50||ns4>s40) continue;
    int nrl=(l>=4)?runlen+1:0;
    if(nrl>4) continue;
    if(!seg_ok(x,l,cl)) continue;
    for(int j=0;j<l;j++) used[cl[j]]=1;
    NB++;COST+=c;NS5=ns5;NS4=ns4;
    int r5=s50-NS5, r4=s40-NS4, rm=c0-COST;
    if(rm>=r5+2*r4 && rm<=r5+4*r4){
      if(NB==B && COST==c0 && NS5==s50 && NS4==s40 && (lb==0||l==lb)){
        int sNB=NB,sC=COST,s5s=NS5,s4s=NS4;
        NB=0;COST=0;NS5=0;NS4=0;
        chain_done(ci,nchains);
        NB=sNB;COST=sC;NS5=s5s;NS4=s4s;
      }
      if(NB<B){
        int ub=NB+(4-((l>=4)?nrl:0))+5*(rm/2);
        if(ub>=B){
          int e=seg_end(x,l);
          for(int nx=0;nx<720;nx++) if(DIST[e][nx]==3) chain_dfs(ci,nchains,nx,nrl);
        }
      }
    }
    NB--;COST-=c;NS5-=(l==4);NS4-=(l<4);
    for(int j=0;j<l;j++) used[cl[j]]=0;
  }
}
int main(int argc,char**argv){
  build();
  if(argc<8){fprintf(stderr,"usage\n");return 1;}
  NQ=atoi(argv[1]);
  int nchains=(argc>=14)?2:1;
  for(int i=0;i<nchains;i++)
    for(int j=0;j<6;j++) Q[i][j]=atoi(argv[2+i*6+j]);
  memset(used,0,sizeof used);
  NB=0;COST=0;NS5=0;NS4=0;NODES=0;CONFIGS=0;COVERS=0;
  chain_dfs(0,nchains,0,0);
  printf("NQ=%d chains=%d chain1done=%lld configs=%lld covers=%lld nodes=%lld %s\n",
         NQ,nchains,C1DONE,CONFIGS,COVERS,NODES,COVERS?"ALIVE":"EMPTY");
  return 0;
}
