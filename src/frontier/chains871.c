/* chains871.c -- INDEPENDENT n=6 hop-chain enumerator (T-n6-871).
 *
 * Written from the raw definitions of proof6.md sections 1,3,7 -- no code
 * shared with approaches/n6/checks/chain6.c.
 *
 *   perms of [6], 720 of them.  rot(p)=p2p3p4p5p6p1, rho(p)=p2p3p4p5p1p6,
 *   d(p,q) = 6 - (longest suffix of p that is a prefix of q).
 *   rotation class C(p) = {rot^i p};  120 classes.
 *   link-path seg(x,l): head crit x, classes C(rho^j x) for j<l (l in 1..5),
 *   end completion rot^-1(rho^{l-1} x).
 *   chain: class-disjoint segs joined by HOPs, i.e. d(end_i, x_{i+1}) = 3.
 *   blocks = #segs, cost = sum(5-l_i), value = blocks - 2*cost.
 *
 * MODES
 *   A  : all l in {4,5}, every one of the 720 head crits  -> run caps
 *   B  : all l in 1..5, head crit 123456 (WLOG relabelling) -> typed value caps
 *   C <CMAX> : Pareto frontier g(cost,a,b) = max blocks, cost <= CMAX
 *   S <CMAX> : refined frontier gS(cost,nshort,a,b) = max blocks
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char P[720][6];
static int NP=720;
static int ROT[720], RHO[720], CLS[720];
static signed char DIST[720][720];
static int idx_of[46656]; /* base-6 code -> perm index */

static int code(const unsigned char*a){int c=0;for(int i=0;i<6;i++)c=c*6+(a[i]-1);return c;}

static void build(void){
  int n=0; unsigned char a[6];
  for(a[0]=1;a[0]<=6;a[0]++)for(a[1]=1;a[1]<=6;a[1]++){if(a[1]==a[0])continue;
   for(a[2]=1;a[2]<=6;a[2]++){if(a[2]==a[0]||a[2]==a[1])continue;
    for(a[3]=1;a[3]<=6;a[3]++){if(a[3]==a[0]||a[3]==a[1]||a[3]==a[2])continue;
     for(a[4]=1;a[4]<=6;a[4]++){if(a[4]==a[0]||a[4]==a[1]||a[4]==a[2]||a[4]==a[3])continue;
      for(a[5]=1;a[5]<=6;a[5]++){int ok=1;for(int i=0;i<5;i++)if(a[5]==a[i])ok=0;if(!ok)continue;
       memcpy(P[n],a,6); n++;}}}}}
  if(n!=720){fprintf(stderr,"perm build failed %d\n",n);exit(1);}
  for(int i=0;i<46656;i++)idx_of[i]=-1;
  for(int i=0;i<720;i++) idx_of[code(P[i])]=i;
  unsigned char t[6];
  for(int i=0;i<720;i++){
    for(int k=0;k<5;k++)t[k]=P[i][k+1]; t[5]=P[i][0]; ROT[i]=idx_of[code(t)];
    t[0]=P[i][1];t[1]=P[i][2];t[2]=P[i][3];t[3]=P[i][4];t[4]=P[i][0];t[5]=P[i][5];
    RHO[i]=idx_of[code(t)];
  }
  /* class id = index of the lexicographically smallest member of the rot-orbit */
  for(int i=0;i<720;i++){int m=i,c=i;for(int k=0;k<5;k++){c=ROT[c];if(c<m)m=c;}CLS[i]=m;}
  {int seen[720];memset(seen,0,sizeof seen);int nc=0;
   for(int i=0;i<720;i++)if(!seen[CLS[i]]){seen[CLS[i]]=1;nc++;}
   if(nc!=120){fprintf(stderr,"class count %d\n",nc);exit(1);} }
  for(int i=0;i<720;i++)for(int j=0;j<720;j++){
    int dd=6;
    for(int k=1;k<=5;k++){int ok=1;for(int t2=0;t2<6-k;t2++)if(P[i][k+t2]!=P[j][t2]){ok=0;break;}
      if(ok){dd=k;break;}}
    DIST[i][j]=(signed char)dd;
  }
}

/* ---- chain enumeration ---- */
static int used[720];          /* class-id -> used */
static int segH[40], segL[40];
static int NB, COST;
static long long NODES;

/* MODE A state */
static int A_maxblocks, A_maxfours, A_interior_four;
/* MODE B state */
static int B_maxvalue, B_cap[4]; /* (a,b) index */
static int B_single;
/* MODE C/S */
static int CMAX;
static int *G;     /* [cost][a][b] */
#define GI(c,a,b) ((c)*4+(a)*2+(b))
static int *GS;    /* [cost][s5][s4][a][b]  s5=#len-4 paths, s4=#len<=3 paths */
#define S4MAX 12
#define GSI(c,s5,s4,a,b) (((((c)*(CMAX+1))+(s5))*(S4MAX+1)+(s4))*4+(a)*2+(b))
static int NS5,NS4;
/* SUF[c][s5][s4][a] = MIN of GS over every COMBINATORIALLY FEASIBLE cell with
   cost c, s5' >= s5, s4' >= s4, either b.  A node may be pruned only when no
   reachable cell can still be improved, so this must be a MIN, not a max, and
   it must range only over cells a chain could actually land in.  A cell is
   declared infeasible only from PROVED necessary conditions:
     cost = (#length-4 paths) + sum over the s4 paths of (5-l), 5-l in {2,3,4}
       => s5 + 2*s4 <= c <= s5 + 4*s4
     r <= s4+1 maximal {4,5}-runs, <= 2 length-4 paths per run (C6-A)
       => s5 <= 2*(s4+1).                                                    */
#define INFV 1000000
static int *SUF;
#define SUFI(c,s5,s4,a) ((((c)*(CMAX+1))+(s5))*(S4MAX+1)*2+(s4)*2+(a))
static int feas(int c,int s5,int s4){
  if(c < s5+2*s4) return 0;
  if(c > s5+4*s4) return 0;
  if(s5 > 2*(s4+1)) return 0;
  return 1;
}
static void rebuild_suf(void){
  for(int c=0;c<=CMAX;c++)for(int a=0;a<2;a++){
    for(int s5=CMAX;s5>=0;s5--)for(int s4=S4MAX;s4>=0;s4--){
      int v=INFV;
      if(feas(c,s5,s4)) for(int b=0;b<2;b++){int t=GS[GSI(c,s5,s4,a,b)]; if(t<v)v=t;}
      if(s5+1<=CMAX){int t=SUF[SUFI(c,s5+1,s4,a)]; if(t<v)v=t;}
      if(s4+1<=S4MAX){int t=SUF[SUFI(c,s5,s4+1,a)]; if(t<v)v=t;}
      SUF[SUFI(c,s5,s4,a)]=v;
    }
  }
}

static int seg_ok(int x,int l,int *cl){
  int y=x;
  for(int j=0;j<l;j++){ cl[j]=CLS[y]; if(used[cl[j]]) return 0;
    for(int t=0;t<j;t++) if(cl[t]==cl[j]) return 0;
    y=RHO[y]; }
  return 1;
}
static int seg_end(int x,int l){ int y=x; for(int j=0;j<l-1;j++)y=RHO[y];
  /* rot^-1 = rot^5 */ for(int k=0;k<5;k++)y=ROT[y]; return y; }

/* ---------- MODE A ---------- */
static int A_run_fours, A_first_l;
static void dfsA(int x){
  NODES++;
  int cl[5];
  for(int l=4;l<=5;l++){
    if(!seg_ok(x,l,cl)) continue;
    for(int j=0;j<l;j++) used[cl[j]]=1;
    segH[NB]=x; segL[NB]=l; NB++;
    if(l==4){A_run_fours++;}
    if(NB>A_maxblocks)A_maxblocks=NB;
    if(A_run_fours>A_maxfours)A_maxfours=A_run_fours;
    /* interior four: after placing, any seg strictly between first and last */
    for(int q=1;q+1<NB;q++) if(segL[q]==4){ if(!A_interior_four){A_interior_four=1;
        fprintf(stderr,"INTERIOR4 lens");for(int r=0;r<NB;r++)fprintf(stderr," %d",segL[r]);
        fprintf(stderr,"\n");} }
    {int e=seg_end(x,l);
    for(int nx=0;nx<720;nx++) if(DIST[e][nx]==3) dfsA(nx);}
    if(l==4){A_run_fours--;}
    NB--;
    for(int j=0;j<l;j++) used[cl[j]]=0;
  }
}

/* ---------- MODE B / C / S ---------- */
static int RUNCAP=4;
/* upper bound on additional blocks given remaining cost budget m and the
   number of blocks already placed in the current {4,5}-run */
static int boundRem(int m,int runlen){
  int b=RUNCAP-runlen; if(b<0)b=0;
  return b + 5*(m/2);
}
static int firstShort;
static void record(int lastShort){
  int a=firstShort,b=lastShort;
  if(COST<=CMAX){
    if(NB>G[GI(COST,a,b)]) G[GI(COST,a,b)]=NB;
    if(GS && NS5<=CMAX && NS4<=S4MAX && NB>GS[GSI(COST,NS5,NS4,a,b)]){
      GS[GSI(COST,NS5,NS4,a,b)]=NB; rebuild_suf(); }
  }
  int v=NB-2*COST;
  int ix=a*2+b;
  if(v>B_cap[ix]) B_cap[ix]=v;
  if(NB==1 && (a||b)) { if(v>B_single) B_single=v; }
  if(v>B_maxvalue) B_maxvalue=v;
}
static void dfsC(int x,int runlen){
  NODES++;
  int cl[5];
  for(int l=1;l<=5;l++){
    int c=5-l;
    if(COST+c>CMAX) continue;
    if(!seg_ok(x,l,cl)) continue;
    for(int j=0;j<l;j++) used[cl[j]]=1;
    segH[NB]=x; segL[NB]=l; NB++; COST+=c; if(l==4)NS5++; else if(l<4)NS4++;
    int nrl = (l>=4)? runlen+1 : 0;
    if(NB==1) firstShort=(l<5);
    if(nrl<=RUNCAP){
      record(l<5);
      int e=seg_end(x,l);
      /* prune: can we still improve anything? */
      int useful=0;
      for(int cc=COST;cc<=CMAX && !useful;cc++){
        int ub=NB+boundRem(cc-COST,nrl);
        for(int bb=0;bb<2;bb++) if(ub>G[GI(cc,firstShort,bb)]) {useful=1;break;}
        if(!useful && GS && NS5<=CMAX && NS4<=S4MAX){
          if(ub>SUF[SUFI(cc,NS5,NS4,firstShort)]) useful=1;
        }
        if(!useful && GS && (NS5>CMAX||NS4>S4MAX)) useful=1;
      }
      if(useful)
        for(int nx=0;nx<720;nx++) if(DIST[e][nx]==3) dfsC(nx,nrl);
    }
    if(l==4)NS5--; else if(l<4)NS4--; COST-=c; NB--;
    for(int j=0;j<l;j++) used[cl[j]]=0;
  }
}

int main(int argc,char**argv){
  build();
  const char*mode=argc>1?argv[1]:"A";
  memset(used,0,sizeof used);
  NB=0;COST=0;NODES=0;NS5=0;NS4=0;
  if(mode[0]=='A'){
    A_maxblocks=0;A_maxfours=0;A_interior_four=0;A_run_fours=0;
    for(int x=0;x<720;x++){ dfsA(x); }
    printf("MODEA starts=all720 nodes=%lld MAXBLOCKS=%d MAXFOURS=%d INTERIOR_FOUR=%d\n",
           NODES,A_maxblocks,A_maxfours,A_interior_four);
    int pass = A_maxblocks==4&&A_maxfours==2&&A_interior_four==0;
    printf(pass?"RUNCAP4 PASS\n":"RUNCAP4 FAIL\n");
    return pass?0:1;        /* the exit code must carry the verdict */
  }
  CMAX = argc>2?atoi(argv[2]):16;
  int want_s = (mode[0]=='S');
  G=malloc(sizeof(int)*4*(CMAX+1));
  for(int i=0;i<4*(CMAX+1);i++)G[i]=-1;
  GS=NULL;
  if(want_s){ size_t n=(size_t)4*(CMAX+1)*(CMAX+1)*(S4MAX+1);
    GS=malloc(sizeof(int)*n); for(size_t i=0;i<n;i++)GS[i]=-1;
    size_t ns=(size_t)2*(CMAX+1)*(CMAX+1)*(S4MAX+1);
    SUF=malloc(sizeof(int)*ns); for(size_t i=0;i<ns;i++)SUF[i]=-1; rebuild_suf(); }
  B_maxvalue=-1000;B_single=-1000;for(int i=0;i<4;i++)B_cap[i]=-1000;
  dfsC(0,0);   /* head crit index 0 = 123456 (WLOG, relabelling) */
  printf("MODE%c CMAX=%d nodes=%lld\n",mode[0],CMAX,NODES);
  printf("cost : g[0,0] g[1,0] g[0,1] g[1,1]\n");
  for(int c=0;c<=CMAX;c++)
    printf("%4d : %6d %6d %6d %6d\n",c,G[GI(c,0,0)],G[GI(c,1,0)],G[GI(c,0,1)],G[GI(c,1,1)]);
  printf("TYPED MAXIMA free=%d shortfirst=%d shortlast=%d bothshort=%d single-short=%d MAXVALUE=%d\n",
         B_cap[0],B_cap[1],B_cap[2],B_cap[3],B_single,B_maxvalue);
  if(want_s){
    printf("REFINED gS(cost,s5,s4,a,b):\n");
    for(int c=0;c<=CMAX;c++)for(int s5=0;s5<=CMAX;s5++)for(int s4=0;s4<=S4MAX;s4++){
      int any=0;for(int i=0;i<4;i++)if(GS[GSI(c,s5,s4,i>>1,i&1)]>=0)any=1;
      if(!any)continue;
      printf("S %d %d %d : %d %d %d %d\n",c,s5,s4,GS[GSI(c,s5,s4,0,0)],GS[GSI(c,s5,s4,1,0)],
             GS[GSI(c,s5,s4,0,1)],GS[GSI(c,s5,s4,1,1)]);
    }
  }
  printf("DONE\n");
  return 0;
}
