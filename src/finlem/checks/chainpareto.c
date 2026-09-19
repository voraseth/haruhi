/* chainpareto.c -- T-n6-tight: independent complete enumeration of the n=6
 * coarse hop-chain Pareto frontier g(c,a,b) for cost c <= CMAX.
 * Abstraction (proof6.md sect.7, re-implemented from its statement, no code
 * shared): a chain is a sequence of pairwise class-disjoint link-path segments
 * seg(x,l) = (head crit x; classes cls(rho^j x), j<l; end rot^-1(rho^(l-1)x)),
 * 1<=l<=5, joined by hops = exact-distance-3 steps from the end completion to
 * the next head crit.  WLOG the first head is 123456 (relabelling commutes with
 * rot,rho,d and is transitive).  cost = sum(5-l), a=1 iff first segment short,
 * b=1 iff last segment short.  NO pruning except the cost budget and the
 * class-disjointness that DEFINE the abstraction => search is complete.
 * Output: table g[c][a][b] (max blocks, -1 if unrealizable) and node count. */
#include <stdio.h>
#include <string.h>
#include <stdint.h>

static int perm[720][6], pidx[1000000];
static int rotp[720], rhop[720], rotinv[720], clsp[720];
static int hop3[720][6];
static long long nodes = 0;
#ifndef CMAX
#define CMAX 15
#endif
static int g[CMAX+1][2][2];
static uint64_t used0, used1;

static int key(const int *p){int k=0;for(int i=0;i<6;i++)k=k*10+p[i];return k;}

static void dfs(int x, int blocks, int cost, int a, int depth){
    nodes++;
    /* try each segment length from head crit x */
    int orb[5]; int q = x;
    for(int l=1;l<=5;l++){
        if(l>1) q = rhop[q];
        orb[l-1] = clsp[q];
        int c = clsp[q];
        if((c<64 ? (used0>>c)&1 : (used1>>(c-64))&1)) break; /* class reuse: no longer segs either */
        int nc = cost + (l<5 ? 0 : 0); /* placeholder */
        (void)nc;
    }
    /* the loop above only finds max extendable l; redo cleanly */
    int maxl = 0; q = x;
    for(int l=1;l<=5;l++){
        if(l>1) q = rhop[q];
        int c = clsp[q];
        if((c<64 ? (used0>>c)&1 : (used1>>(c-64))&1)) break;
        orb[l-1]=c; maxl=l;
    }
    for(int l=1;l<=maxl;l++){
        int addc = 5-l;
        int nc = cost + addc;
        if(nc > CMAX) continue;
        /* place segment */
        for(int j=0;j<l;j++){int c=orb[j]; if(c<64)used0|=1ULL<<c; else used1|=1ULL<<(c-64);}
        int na = (blocks==0)? (l<5) : a;
        int nb = (l<5);
        int nbl = blocks+1;
        if(nbl > g[nc][na][nb]) g[nc][na][nb] = nbl;
        /* hop onward */
        int hq = x; for(int j=1;j<l;j++) hq = rhop[hq];
        int end = rotinv[hq];
        for(int t=0;t<6;t++) dfs(hop3[end][t], nbl, nc, na, depth+1);
        for(int j=0;j<l;j++){int c=orb[j]; if(c<64)used0&=~(1ULL<<c); else used1&=~(1ULL<<(c-64));}
    }
}

int main(void){
    /* build the 720 permutations of 123456 in lex order */
    int a[6]={1,2,3,4,5,6}, n=0;
    /* Heap-free: simple recursive gen via loops */
    for(int i0=0;i0<6;i0++)for(int i1=0;i1<6;i1++)for(int i2=0;i2<6;i2++)
    for(int i3=0;i3<6;i3++)for(int i4=0;i4<6;i4++)for(int i5=0;i5<6;i5++){
        int u[6]={i0,i1,i2,i3,i4,i5}, m=0; int p[6];
        for(int i=0;i<6;i++){for(int j=0;j<i;j++) if(u[j]==u[i]) m=1; p[i]=u[i]+1;}
        if(m) continue;
        memcpy(perm[n],p,sizeof p); pidx[key(p)]=n; n++;
    }
    (void)a;
    if(n!=720){printf("GENFAIL\n");return 1;}
    for(int i=0;i<720;i++){
        int p[6],r[6];
        memcpy(p,perm[i],sizeof p);
        for(int j=0;j<6;j++) r[j]=p[(j+1)%6];        /* rot */
        rotp[i]=pidx[key(r)];
        int rh[6]={p[1],p[2],p[3],p[4],p[0],p[5]};    /* rho */
        rhop[i]=pidx[key(rh)];
        int ri[6]; for(int j=0;j<6;j++) ri[(j+1)%6]=p[j]; /* rot^-1 */
        rotinv[i]=pidx[key(ri)];
    }
    /* classes: canonical = min over rotations */
    int cl=0; int cid[720]; for(int i=0;i<720;i++) cid[i]=-1;
    for(int i=0;i<720;i++){
        if(cid[i]>=0) continue;
        int q=i, mn=i;
        for(int t=0;t<5;t++){ q=rotp[q]; if(q<mn) mn=q; }
        if(mn==i){ q=i; for(int t=0;t<6;t++){ cid[q]=cl; q=rotp[q]; } cl++; }
    }
    if(cl!=120){printf("CLSFAIL %d\n",cl);return 1;}
    for(int i=0;i<720;i++) clsp[i]=cid[i];
    /* d=3 successors: q[0..2] = p[3..5], q[3..5] = perm of p[0..2] (all give d=3 exactly) */
    for(int i=0;i<720;i++){
        int *p=perm[i]; int t=0;
        int per3[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
        for(int s=0;s<6;s++){
            int q[6]={p[3],p[4],p[5],p[per3[s][0]],p[per3[s][1]],p[per3[s][2]]};
            hop3[i][t++]=pidx[key(q)];
        }
    }
    memset(g,-1,sizeof g);
    used0=used1=0;
    dfs(pidx[key((int[]){1,2,3,4,5,6})],0,0,0,0);
    printf("nodes=%lld CMAX=%d\n",nodes,CMAX);
    printf("cost  free  sf  sl  ss   (running max in cost)\n");
    int run[2][2]={{-1,-1},{-1,-1}};
    for(int c=0;c<=CMAX;c++){
        for(int x=0;x<2;x++)for(int y=0;y<2;y++) if(g[c][x][y]>run[x][y]) run[x][y]=g[c][x][y];
        printf("%2d   %3d  %3d %3d %3d\n",c,run[0][0],run[1][0],run[0][1],run[1][1]);
    }
    return 0;
}
