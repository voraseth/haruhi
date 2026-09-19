/* realize3.c -- v3: adds the d>=4 join moves for the (15,1,0) and (10,2,0)
 * corners (X4h in {1,2}; every d>=4 transition there is d=4 exactly, I6):
 *   (c) d4-jump: a chain ends by emitting a d=4 completion exit landing on the
 *       head of an m=1 component (24 exact-d=4 successors);
 *   (d) d4-close: the d=4 lands on an M2's closer head K1 (a singleton chain);
 *       the M2's launcher K2 starts the next chain (R1-type acyclicity makes
 *       the join sequence linear exactly as in R1').
 * Derived from realize2.c -- T-n6-tight stage-2 realizability engine, v2: whole (20,0,0)
 * column.  Extends realize.c (v1, kept for the record) with:
 *   - up to two M2 components, closed in LINEAR order (lemma R1': the
 *     "chain closes into M2" relation is acyclic, hence linear: q1's chain
 *     closes the first M2, each launcher the next, the last one ends at the
 *     global end);
 *   - the bq1 = 1 start (q1 is the M2 closer's head: the M2 sits at 123456
 *     and the construction starts from its launcher K2);
 *   - M2 cost budgets passed as an s2 multiset (l1+l2 = s2, all splits tried).
 * All census rows of (20,0,0) e=1..9 have a3 = c2 = 0, so no M3/2-cycle
 * pieces are needed.  Original header:
 * realize.c -- T-n6-tight stage-2 realizability of a pinned (20,0,0) census.
 * Model (all conditions PROVED necessary in proof_tight.md sects. 3-5 + R1):
 *   - chain Q: q1's m=1 comp (head 123456 WLOG) + mids (m=1 comps) joined by
 *     exact-d=3 hops from end completion rot^-1(rho^(l-1) head) to next head;
 *     ends by hopping onto the M2 closer K1 (mode e9/e8) or at the global end
 *     (mode ctrl872);
 *   - M2 comp: K1(l1 crits) nc K2(l2 crits) at consecutive rho positions;
 *   - chain A: starts at K2, mids by d=3 hops, ends at global end;
 *   - lemma R1 (temporal): chain Q, not chain A, ends at the closer;
 *   - all component arcs pairwise position-disjoint, classes covered <= 1;
 *   - endgame: remaining classes exactly covered by NCYC full-orbit cycles
 *     (4 crits + 1 nc each) on virgin orbits (TC2c).
 * Complete search: no pruning beyond the defining constraints + node cap.
 * SAT => census realizable at this level.  UNSAT(exhausted) => CELL EMPTY. */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>

static int perm[720][6], pidx[1000000];
static int rhop[720], rotp[720], rotinv[720], clsp[720];
static int hop3[720][6];
static int d4s[720][24];
static int orbid[720], orbpos[720];      /* orbit id 0..143, position 0..4 */
static int orbperm[144][5];              /* orbit -> perms by position */
static int cls_orbs[120][6], cls_pos[120][6], cls_norb[120];
static uint64_t cov0, cov1;              /* covered classes bitmask */
static uint8_t pmask[144];               /* used positions per orbit */
static long long nodes = 0, CAP = 4000000000LL;
static int nrem[6];                      /* remaining m=1 comps by length 1..5 */
static int ncyc_rem, m2_rem;
static int m2sums[6];
static int d4_rem = 0;                    /* remaining M2s by s2=l1+l2 (2..4) */
static int found = 0;
static int npieces = 0, maxpieces = 0;
static long long egame_calls = 0; static int egame_best = 999;
static int chainonly = 0, loose = 0;
static int seq_kind[40], seq_head[40], seq_l[40], seq_n = 0;
static int best_kind[40], best_head[40], best_l[40], best_n = 0;
static void rec_push(int k,int h,int l){ seq_kind[seq_n]=k; seq_head[seq_n]=h; seq_l[seq_n]=l; seq_n++;
    if(seq_n>best_n){ best_n=seq_n; memcpy(best_kind,seq_kind,sizeof seq_kind);
        memcpy(best_head,seq_head,sizeof seq_head); memcpy(best_l,seq_l,sizeof seq_l);} }


static int key(const int *p){int k=0;for(int i=0;i<6;i++)k=k*10+p[i];return k;}
static inline int covget(int c){ return c<64 ? (cov0>>c)&1 : (cov1>>(c-64))&1; }
static inline void covset(int c){ if(c<64) cov0|=1ULL<<c; else cov1|=1ULL<<(c-64); }
static inline void covclr(int c){ if(c<64) cov0&=~(1ULL<<c); else cov1&=~(1ULL<<(c-64)); }

/* place an arc of l consecutive rho-positions from perm x, all crits.
 * returns 0 if blocked; else records for undo (positions+classes). */
static int place_arc(int x, int l, int *undo){
    int q = x;
    for(int j=0;j<l;j++){
        int o=orbid[q], p=orbpos[q], c=clsp[q];
        if((pmask[o]>>p)&1) { for(int k=j-1;k>=0;k--){int qq=undo[k];pmask[orbid[qq]]&=~(1<<orbpos[qq]);covclr(clsp[qq]);} return 0; }
        if(covget(c))       { for(int k=j-1;k>=0;k--){int qq=undo[k];pmask[orbid[qq]]&=~(1<<orbpos[qq]);covclr(clsp[qq]);} return 0; }
        pmask[o]|=1<<p; covset(c); undo[j]=q;
        q = rhop[q];
    }
    return 1;
}
static void unplace_arc(int l, int *undo){
    for(int k=l-1;k>=0;k--){int q=undo[k];pmask[orbid[q]]&=~(1<<orbpos[q]);covclr(clsp[q]);}
}

static int endgame(void){
    nodes++; egame_calls++;
    if(chainonly) return 1;
    { int unc=0; for(int i=0;i<120;i++) if(!covget(i)) unc++;
      if(unc<egame_best) egame_best=unc; }
    if(nodes>CAP){ printf("NODE_CAP_HIT\n"); exit(3); }
    if(ncyc_rem==0) return cov0==~0ULL && cov1==(1ULL<<56)-1;
    /* lowest uncovered class */
    int c=-1;
    for(int i=0;i<120;i++) if(!covget(i)){ c=i; break; }
    if(c<0) return 0;                      /* classes done but cycles remain */
    for(int t=0;t<cls_norb[c];t++){
        int o=cls_orbs[c][t], pc=cls_pos[c][t];
        if(pmask[o]) continue;             /* cycle needs a virgin orbit */
        for(int nc=0;nc<5;nc++){
            if(nc==pc) continue;
            int ok=1;
            for(int j=0;j<5;j++) if(j!=nc && covget(clsp[orbperm[o][j]])) { ok=0; break; }
            if(!ok) continue;
            pmask[o]=31; ncyc_rem--;
            for(int j=0;j<5;j++) if(j!=nc) covset(clsp[orbperm[o][j]]);
            if(endgame()) return 1;
            for(int j=0;j<5;j++) if(j!=nc) covclr(clsp[orbperm[o][j]]);
            ncyc_rem++; pmask[o]=0;
        }
    }
    return 0;
}

static int arc_end(int x,int l){ int q=x; for(int j=1;j<l;j++) q=rhop[q]; return rotinv[q]; }

static int dfsQ(int end){
    nodes++;
    if(nodes>CAP){ printf("NODE_CAP_HIT\n"); exit(3); }
    int undo[5], u2[6];
    if(m2_rem==0 && d4_rem==0){           /* all joins placed: may end at global end */
        int left=0; for(int l=1;l<=5;l++) left+=nrem[l];
        if(left==0) return endgame();
    }
    for(int t=0;t<(loose?30:6);t++){
        int x = t<6 ? hop3[end][t] : d4s[end][t-6];
        /* (a) continue with a mid */
        for(int l=5;l>=1;l--){
            if(!nrem[l]) continue;
            if(!place_arc(x,l,undo)) continue;
            nrem[l]--; npieces++; if(npieces>maxpieces)maxpieces=npieces; rec_push(1,x,l);
            if(dfsQ(arc_end(x,l))) return 1;
            seq_n--; npieces--; nrem[l]++;
            unplace_arc(l,undo);
        }
        /* (b) close: hop onto K1, place M2, next chain from K2 (linear order, R1') */
        if(m2_rem){
            for(int s2=2;s2<=4;s2++){ if(!m2sums[s2]) continue;
            for(int l1=1;l1<s2;l1++){
                int l2=s2-l1, span=l1+1+l2;
                /* positions x..rho^(span-1)x; crits except index l1 */
                int q=x, ok=1, cnt=0;
                for(int j=0;j<span;j++){
                    int o=orbid[q],p=orbpos[q];
                    if((pmask[o]>>p)&1){ok=0;break;}
                    if(j!=l1 && covget(clsp[q])){ok=0;break;}
                    q=rhop[q];
                }
                if(!ok) continue;
                q=x;
                for(int j=0;j<span;j++){ pmask[orbid[q]]|=1<<orbpos[q]; if(j!=l1){covset(clsp[q]);} u2[j]=q; q=rhop[q]; }
                m2_rem--; m2sums[s2]--; npieces++; if(npieces>maxpieces)maxpieces=npieces; rec_push(3,x,l1*10+l2);
                int k2h=x; for(int j=0;j<l1+1;j++) k2h=rhop[k2h];
                if(dfsQ(arc_end(k2h,l2))) return 1;
                seq_n--; npieces--; m2sums[s2]++; m2_rem++;
                for(int j=span-1;j>=0;j--){int qq=u2[j];pmask[orbid[qq]]&=~(1<<orbpos[qq]); if(j!=l1) covclr(clsp[qq]);}
            }}
        }
    }
    /* (c) d4-jump onto an m=1 arc; (d) d4-close onto an M2's K1 */
    if(d4_rem){
        int undo2[5], u3[6];
        for(int t=0;t<24;t++){
            int x=d4s[end][t];
            for(int l=5;l>=1;l--){
                if(!nrem[l]) continue;
                if(!place_arc(x,l,undo2)) continue;
                nrem[l]--; d4_rem--; npieces++; if(npieces>maxpieces)maxpieces=npieces; rec_push(4,x,l);
                if(dfsQ(arc_end(x,l))) return 1;
                seq_n--; npieces--; d4_rem++; nrem[l]++;
                unplace_arc(l,undo2);
            }
            if(m2_rem){
                for(int s2=2;s2<=4;s2++){ if(!m2sums[s2]) continue;
                for(int l1=1;l1<s2;l1++){
                    int l2=s2-l1, span=l1+1+l2, q=x, ok=1;
                    for(int j=0;j<span;j++){
                        if((pmask[orbid[q]]>>orbpos[q])&1){ok=0;break;}
                        if(j!=l1 && covget(clsp[q])){ok=0;break;}
                        q=rhop[q];
                    }
                    if(!ok) continue;
                    q=x;
                    for(int j=0;j<span;j++){ pmask[orbid[q]]|=1<<orbpos[q]; if(j!=l1)covset(clsp[q]); u3[j]=q; q=rhop[q]; }
                    m2_rem--; m2sums[s2]--; d4_rem--; npieces++; if(npieces>maxpieces)maxpieces=npieces; rec_push(5,x,l1*10+l2);
                    int k2h=x; for(int j=0;j<l1+1;j++) k2h=rhop[k2h];
                    if(dfsQ(arc_end(k2h,l2))) return 1;
                    seq_n--; npieces--; d4_rem++; m2sums[s2]++; m2_rem++;
                    q=x;
                    for(int j=0;j<span;j++){ pmask[orbid[q]]&=~(1<<orbpos[q]); if(j!=l1)covclr(clsp[q]); q=rhop[q]; }
                }}
            }
        }
    }
    return 0;
}

int main(int argc, char **argv){
    /* argv: n5 n4 n3 n2 n1 ncyc m2spec cap
       m2spec: "0" none, else e.g. "13,31,22" list of l1l2 */
    for(int i0=0;i0<6;i0++)for(int i1=0;i1<6;i1++)for(int i2=0;i2<6;i2++)
    for(int i3=0;i3<6;i3++)for(int i4=0;i4<6;i4++)for(int i5=0;i5<6;i5++){
        int u[6]={i0,i1,i2,i3,i4,i5},m=0,p[6];
        for(int i=0;i<6;i++){for(int j=0;j<i;j++)if(u[j]==u[i])m=1;p[i]=u[i]+1;}
        if(m)continue;
        static int n=0; memcpy(perm[n],p,sizeof p); pidx[key(p)]=n; n++;
    }
    for(int i=0;i<720;i++){
        int p[6],r[6],rh[6],ri[6];
        memcpy(p,perm[i],sizeof p);
        for(int j=0;j<6;j++) r[j]=p[(j+1)%6];
        rotp[i]=pidx[key(r)];
        rh[0]=p[1];rh[1]=p[2];rh[2]=p[3];rh[3]=p[4];rh[4]=p[0];rh[5]=p[5];
        rhop[i]=pidx[key(rh)];
        for(int j=0;j<6;j++) ri[(j+1)%6]=p[j];
        rotinv[i]=pidx[key(ri)];
        int per3[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
        for(int s=0;s<6;s++){
            int q[6]={p[3],p[4],p[5],p[per3[s][0]],p[per3[s][1]],p[per3[s][2]]};
            hop3[i][s]=pidx[key(q)];
        }
        /* d=4 successors: q[0:2]=p[4:6], q[2:6] = perm of p[0:4] (24, all d=4) */
        {   int idx4[24][4], t4=0;
            for(int a=0;a<4;a++)for(int b=0;b<4;b++)for(int c=0;c<4;c++)for(int d=0;d<4;d++){
                if(a==b||a==c||a==d||b==c||b==d||c==d) continue;
                idx4[t4][0]=a; idx4[t4][1]=b; idx4[t4][2]=c; idx4[t4][3]=d; t4++;
            }
            for(int s=0;s<24;s++){
                int q[6]={p[4],p[5],p[idx4[s][0]],p[idx4[s][1]],p[idx4[s][2]],p[idx4[s][3]]};
                d4s[i][s]=pidx[key(q)];
            }
        }
    }
    /* classes */
    {   int cid[720]; for(int i=0;i<720;i++) cid[i]=-1; int cl=0;
        for(int i=0;i<720;i++){ if(cid[i]>=0) continue; int q=i,mn=i;
            for(int t=0;t<5;t++){q=rotp[q]; if(q<mn)mn=q;}
            if(mn==i){q=i; for(int t=0;t<6;t++){cid[q]=cl;q=rotp[q];} cl++; } }
        for(int i=0;i<720;i++) clsp[i]=cid[i];
        if(cl!=120){printf("CLSFAIL\n");return 1;} }
    /* orbits */
    {   int done[720]; memset(done,0,sizeof done); int no=0;
        for(int i=0;i<720;i++){ if(done[i]) continue; int q=i;
            for(int j=0;j<5;j++){ orbid[q]=no; orbpos[q]=j; orbperm[no][j]=q; done[q]=1; q=rhop[q]; }
            if(q!=i){printf("ORBFAIL\n");return 1;} no++; }
        if(no!=144){printf("ORBFAIL2\n");return 1;} }
    memset(cls_norb,0,sizeof cls_norb);
    for(int o=0;o<144;o++)for(int j=0;j<5;j++){
        int c=clsp[orbperm[o][j]];
        cls_orbs[c][cls_norb[c]]=o; cls_pos[c][cls_norb[c]]=j; cls_norb[c]++;
    }
    for(int c=0;c<120;c++) if(cls_norb[c]!=6){printf("CLSORBFAIL\n");return 1;}

    if(argc<10){printf("usage: realize3 n5 n4 n3 n2 n1 ncyc s2list bq1 nd4 [cap]\n");return 1;}
    nrem[5]=atoi(argv[1]); nrem[4]=atoi(argv[2]); nrem[3]=atoi(argv[3]);
    nrem[2]=atoi(argv[4]); nrem[1]=atoi(argv[5]);
    ncyc_rem=atoi(argv[6]);
    memset(m2sums,0,sizeof m2sums); m2_rem=0;
    if(strcmp(argv[7],"0")){
        char *s=argv[7], *tok=strtok(s,",");
        while(tok){ int v=atoi(tok); m2sums[v]++; m2_rem++; tok=strtok(NULL,","); }
    }
    int bq1=atoi(argv[8]);
    d4_rem=atoi(argv[9]);
    if(argc>10) CAP=atoll(argv[10]);
    /* E-9: instance consistency -- the piece multiset must cover the 120
       rotation classes exactly.  See mysweep.c for the rationale. */
    {
        int tot = 5*nrem[5] + 4*nrem[4] + 3*nrem[3] + 2*nrem[2] + 1*nrem[1]
                  + 4*ncyc_rem;
        for(int v = 2; v <= 4; v++) tot += v * m2sums[v];
        if(tot != 120){
            printf("INSTFAIL tot=%d != 120\n", tot);
            return 3;
        }
    }
    if(getenv("CHAINONLY")) chainonly=1;
    if(getenv("LOOSE")) loose=1;         /* falsification probe: mids may join by d=3 OR d=4 */
    int q1=pidx[key((int[]){1,2,3,4,5,6})];
    int undo[5], u2[6];
    if(!bq1){
        for(int l=5;l>=1;l--){
            if(!nrem[l]) continue;
            if(!place_arc(q1,l,undo)) continue;
            nrem[l]--;
            if(dfsQ(arc_end(q1,l))){ found=1; nrem[l]++; unplace_arc(l,undo); break; }
            nrem[l]++;
            unplace_arc(l,undo);
        }
    } else {
        /* q1 is the K1 head of an M2 at 123456; start from its K2 */
        for(int s2=2;s2<=4 && !found;s2++){ if(!m2sums[s2]) continue;
        for(int l1=1;l1<s2 && !found;l1++){
            int l2=s2-l1, span=l1+1+l2, q=q1, ok=1;
            for(int j=0;j<span;j++){
                if((pmask[orbid[q]]>>orbpos[q])&1){ok=0;break;}
                if(j!=l1 && covget(clsp[q])){ok=0;break;}
                q=rhop[q];
            }
            if(!ok) continue;
            q=q1;
            for(int j=0;j<span;j++){ pmask[orbid[q]]|=1<<orbpos[q]; if(j!=l1)covset(clsp[q]); u2[j]=q; q=rhop[q]; }
            m2_rem--; m2sums[s2]--;
            int k2h=q1; for(int j=0;j<l1+1;j++) k2h=rhop[k2h];
            if(dfsQ(arc_end(k2h,l2))) found=1;
            m2sums[s2]++; m2_rem++;
            q=q1;
            for(int j=0;j<span;j++){ pmask[orbid[q]]&=~(1<<orbpos[q]); if(j!=l1)covclr(clsp[q]); q=rhop[q]; }
        }}
    }
    printf("%s nodes=%lld maxpieces=%d egame_calls=%lld egame_minuncov=%d EXHAUSTED\n",
           found?"SAT":"UNSAT", nodes, maxpieces, egame_calls, egame_best);
    printf("deepest trace (kind 1=Qmid 2=Amid 3=M2; head perm; l):\n");
    for(int i=0;i<best_n;i++){
        int *p=perm[best_head[i]];
        printf("  %c head=%d%d%d%d%d%d l=%d\n", best_kind[i]==1?'Q':best_kind[i]==2?'A':'M',
               p[0],p[1],p[2],p[3],p[4],p[5],best_l[i]);
    }
    return found?0:2;
}
