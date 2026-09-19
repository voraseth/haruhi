/* e9exact.c — EXACT (exhaustive) search of the low-re-entry sector of n = 6.
 *
 * S-n6-lowe.  Generalises approaches/n6build/src/e0exact.c from e = 0 to
 * arbitrary e, keeping the segment algebra.  Derived here from raw definitions.
 *
 * MODEL (all constants n = 6).
 *  A superpermutation's first-occurrence order q_1..q_720 satisfies
 *      L >= 6 + sum_k d(q_k,q_{k+1}),  d(p,q) = 6 - (longest suffix of p that
 *  is a prefix of q), and the overlap concatenation of ANY order of the 720
 *  permutations IS a superpermutation of length exactly 6 + sum d.  Hence
 *      L(6) = 6 + min over Hamiltonian paths of sum d,
 *  so searching Hamiltonian paths with sum d = L-6 is a COMPLETE search of
 *  the length-L question (no slack term survives).
 *
 *  RUNS.  A run is a maximal block joined by d=1 steps; d=1 is q -> rot(q),
 *  so a run is an arc of a rotation class (120 classes of 6).  With
 *  R = 120 + e runs there are 720-R arcs of cost 1 and R-1 = 119+e
 *  transitions of cost >= 2, and
 *      L = 6 + (720-R) + sum_{d>=2} d = 844 + e + EXCESS,  EXCESS = sum (d-2).
 *  Writing h = #{d>=3} and X4 = sum_{d>=4}(d-3), EXCESS = h + X4, and with
 *  S = h+1 SEGMENTS (maximal chains of cost-2 transitions)
 *      L = 843 + e + S + X4.
 *  L = 871  <=>  e + S + X4 = 28.
 *
 *  COST-2 STEPS.  From a run end x = x1..x6 the two d=2 successors are
 *  rot^2(x) = x3x4x5x6x1x2 (SAME class: a RE-ENTRY skipping rot(x)) and
 *  sig(x) = x3x4x5x6x2x1 (a different class: a LINK).  So every cost-2 step
 *  has exactly 2 candidates.  A cost-3 step has 6, cost-4 has 24, cost-5 120,
 *  cost-6 566.  At X4 = 0 every heavy step is d = 3 exactly (6 candidates).
 *
 *  WLOG the first permutation is 123456 (relabelling {1..6} acts freely and
 *  transitively on the 720 permutations and commutes with rot and d).
 *
 * Usage: e9exact <E> <S> <X4> <maxnodes> <outfile>
 *   enumerates EVERY walk with exactly 120+E runs, exactly S-1 heavy
 *   transitions and heavy excess exactly X4; L = 843+E+S+X4.
 */
#include "perm6.h"
#include <time.h>

static int SIGM[NP];
static int NBR[NP][7][600];
static int NNB[NP][7];
static int NARC[64];

static int E,S,X4,R,ZBUD,NOQ2;
static int ROTI[NP];
static unsigned long long nodes=0, maxnodes=0;
static unsigned char cmask[NC];
static int needruns, ncls, Pused, uperms;
static int nsol=0;
static FILE *OUT;
static int rs[160], rl[160], rj[160];
static time_t T0;
static unsigned long long nextrep;

#define ISUSED(t) ((cmask[CLS[t]]>>PHASE[t])&1)

static void record(void){
    nsol++;
    fprintf(OUT,"SOL E=%d S=%d X4=%d L=%d\n",E,S,X4,843+E+S+X4);
    for(int i=0;i<R;i++) fprintf(OUT,"RUN %d %d %d\n",rs[i],rl[i],rj[i]);
    fprintf(OUT,"ENDSOL\n");
    fflush(OUT);
}

static void place(int k,int g,int y,int x4u,int fb,int nab,int zb){
    nodes++;
    if(nodes>=nextrep){ nextrep+=1000000000ULL;
        fprintf(stderr,"[%.0fs] E=%d S=%d X4=%d nodes=%llu sols=%d\n",
                difftime(time(0),T0),E,S,X4,nodes,nsol); fflush(stderr); }
    if(nodes>maxnodes) return;
    int c=CLS[y];
    int oldm=cmask[c];
    int basearc=NARC[oldm];
    int newcls=(oldm==0);
    int sv_need=needruns, sv_ncls=ncls, sv_P=Pused, sv_U=uperms;
    int m=oldm, p=y;
    for(int l=1;l<=6;l++){
        if(l>1) p=ROT[p];
        int b=1<<PHASE[p];
        if(m&b) break;
        m|=b;
        cmask[c]=m;
        needruns = sv_need - basearc + NARC[m];
        ncls     = sv_ncls + (newcls?1:0);
        Pused    = sv_P + (l<6?1:0);
        uperms   = sv_U + l;
        rs[k]=y; rl[k]=l;
        int nfb=(l==6)?fb+1:0;
        int placed=k+1, rrem=R-placed, U=720-uperms;
        int ecur=placed-ncls, jrem=S-1-g;
        if(rrem==0){
            if(U==0 && jrem==0 && x4u==X4) record();
        }else if(ecur<=E && rrem>=needruns && rrem<=U && 6*rrem>=U
                 && rrem>=jrem && Pused<=2*E
                 && rrem <= (5-nfb) + 5*(S-1-g) + 6*(2*E-Pused)){
            int end=p, t;
            int srccomp = (m==63);
            /* (a) cost-2 LINK: t = sig(end), a different class */
            t=SIGM[end];
            if(!ISUSED(t)){
                int ab = ISUSED(ROTI[t]);
                if(!ab){ rj[placed]=2; place(placed,g,t,x4u,nfb,nab,zb); }
                else if(srccomp){ if(nab<E){ rj[placed]=2; place(placed,g,t,x4u,nfb,nab+1,zb); } }
                else if(zb>0){ rj[placed]=2; place(placed,g,t,x4u,nfb,nab,zb-1); }
            }
            /* (b) cost-2 RE-ENTRY: t = rot^2(end), same class (Q2 step) */
            if(nodes<=maxnodes && !NOQ2){
                t=ROT[ROT[end]];
                if(!ISUSED(t)){
                    int ab = ISUSED(ROTI[t]);
                    if(!ab){ rj[placed]=2; place(placed,g,t,x4u,nfb,nab,zb); }
                    else if(zb>0){ rj[placed]=2; place(placed,g,t,x4u,nfb,nab,zb-1); }
                }
            }
            /* (c) HEAVY: Z counts one violation per incomplete source and one
                  per abut landing (zp3 and zh in the registered accounting). */
            if(nodes<=maxnodes && jrem>0){
                int dmax=3+(X4-x4u); if(dmax>6) dmax=6;
                for(int d=3; d<=dmax; d++){
                    int nn=NNB[end][d];
                    for(int i=0;i<nn;i++){
                        int q=NBR[end][d][i];
                        if(ISUSED(q)) continue;
                        int v = (srccomp?0:1) + (ISUSED(ROTI[q])?1:0);
                        if(v>zb) continue;
                        rj[placed]=d;
                        place(placed,g+1,q,x4u+d-3,0,nab,zb-v);
                        if(nodes>maxnodes) break;
                    }
                    if(nodes>maxnodes) break;
                }
            }
        }
        needruns=sv_need; ncls=sv_ncls; Pused=sv_P; uperms=sv_U;
        if(nodes>maxnodes) break;
    }
    cmask[c]=oldm;
}

int main(int argc,char**argv){
    if(argc<8){fprintf(stderr,"usage: e9exact E S X4 ZBUD NOQ2 maxnodes outfile\n");return 2;}
    perm6_init();
    for(int p=0;p<NP;p++){
        unsigned char b[6];
        b[0]=P[p][2];b[1]=P[p][3];b[2]=P[p][4];b[3]=P[p][5];b[4]=P[p][1];b[5]=P[p][0];
        SIGM[p]=PIDX[code6(b)];
    }
    /* self-checks on the model, from the definitions */
    for(int p=0;p<NP;p++){
        if(DIST[p][SIGM[p]]!=2){fprintf(stderr,"sig not d=2\n");return 2;}
        if(CLS[SIGM[p]]==CLS[p]){fprintf(stderr,"sig same class\n");return 2;}
        if(DIST[p][ROT[ROT[p]]]!=2){fprintf(stderr,"rot2 not d=2\n");return 2;}
        int cnt=0; for(int q=0;q<NP;q++) if(q!=p&&DIST[p][q]==2) cnt++;
        if(cnt!=2){fprintf(stderr,"d=2 outdeg %d\n",cnt);return 2;}
    }
    {   int od[7]={0,0,0,0,0,0,0};
        for(int q=1;q<NP;q++) od[DIST[0][q]]++;
        if(od[1]!=1||od[2]!=2||od[3]!=6||od[4]!=24||od[5]!=120||od[6]!=566){
            fprintf(stderr,"outdeg profile %d %d %d %d %d %d\n",od[1],od[2],od[3],od[4],od[5],od[6]);
            return 2; }
    }
    for(int p=0;p<NP;p++){ for(int d=0;d<7;d++) NNB[p][d]=0;
        for(int q=0;q<NP;q++){ if(q==p) continue; int d=DIST[p][q];
            if(d>=3&&d<=6&&NNB[p][d]<600) NBR[p][d][NNB[p][d]++]=q; } }
    /* NARC[m] = number of maximal cyclic blocks of UNUSED positions in mask m */
    for(int m=0;m<64;m++){
        if(m==0){NARC[m]=1;continue;}
        if(m==63){NARC[m]=0;continue;}
        int a=0;
        for(int i=0;i<6;i++){ int prev=(i+5)%6;
            if(!((m>>i)&1) && ((m>>prev)&1)) a++; }
        NARC[m]=a;
    }
    E=atoi(argv[1]); S=atoi(argv[2]); X4=atoi(argv[3]);
    ZBUD=atoi(argv[4]); NOQ2=atoi(argv[5]);
    maxnodes=strtoull(argv[6],0,10);
    R=120+E;
    OUT=fopen(argv[7],"w");
    if(!OUT){fprintf(stderr,"cannot open out\n");return 2;}
    fprintf(OUT,"E=%d S=%d X4=%d ZBUD=%d NOQ2=%d R=%d L=%d\n",E,S,X4,ZBUD,NOQ2,R,843+E+S+X4);
    fflush(OUT);
    memset(cmask,0,sizeof cmask);
    needruns=120; ncls=0; Pused=0; uperms=0;
    T0=time(0); nextrep=1000000000ULL;
    rj[0]=0;
    for(int p=0;p<NP;p++){int x=p;for(int i=0;i<5;i++)x=ROT[x];ROTI[p]=x;}
    for(int p=0;p<NP;p++) if(ROT[ROTI[p]]!=p){fprintf(stderr,"roti\n");return 2;}
    place(0,0,0,0,0,0,ZBUD);
    double sec=difftime(time(0),T0);
    fprintf(OUT,"nodes=%llu solutions=%d seconds=%.0f %s\n",
            nodes,nsol,sec,nodes>maxnodes?"NODE_CAP_HIT":"EXHAUSTED");
    fclose(OUT);
    printf("E=%d S=%d X4=%d Z<=%d NOQ2=%d L=%d nodes=%llu solutions=%d sec=%.0f %s\n",
           E,S,X4,ZBUD,NOQ2,843+E+S+X4,nodes,nsol,sec,nodes>maxnodes?"NODE_CAP_HIT":"EXHAUSTED");
    return 0;
}
