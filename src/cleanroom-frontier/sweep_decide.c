/* n6c12 clean-room re-derivation of the coarse chain-capacity frontier g(c,a,b).
 *
 * Domain (paper, Appendix C.2.12 "abstract chain"):
 *   - 720 permutations of {1..6}; rot(p)=p2p3p4p5p6p1; rho(p)=p2p3p4p5p1p6.
 *   - C(p) = rotation class of p (120 classes of 6).
 *   - A segment (link-path) with head x and length l occupies classes
 *     C(rho^j x) for j<l (all pairwise fresh) and ends at the completion
 *     rot^{-1}(rho^{l-1} x).
 *   - Consecutive segments joined by a transition of cost exactly 3:
 *     d(z,y)=3 where z is the previous segment's completion and y the next head.
 *   - cost of a chain = sum over members of deficiency (5-l).
 *   - blocks = number of member paths; a = [first path short], b = [last short].
 * Head normalized to 123456 (relabelling is transitive and commutes with
 * rot, rho, d).
 *
 * Gate: optional run cap r<=4 (Lemma capacity(1) / C6-A).  -g0 disables it.
 * No block-bound pruning of any kind: exhaustive over cost <= CMAX.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <time.h>

#define NP 720
#define NC 120
#define MAXCOST 32

static int permw[NP][6];
static int rho_[NP], rotinv_[NP], cls_[NP];
static int succ3_[NP][6];

static int CMAX = 12;
static int USE_GATE = 1;

typedef struct { uint64_t w[2]; } Mask;
#define MSET(m,c) ((m).w[(c)>>6] |= (1ULL<<((c)&63)))
#define MCLR(m,c) ((m).w[(c)>>6] &= ~(1ULL<<((c)&63)))
#define MGET(m,c) (((m).w[(c)>>6] >> ((c)&63)) & 1ULL)

/* ---- permutation indexing (lexicographic rank) ---- */
static int fact[7] = {1,1,2,6,24,120,720};
static int rankp(const int *w) {
    int used[7]={0}, r=0;
    for (int i=0;i<6;i++){
        int c=0;
        for (int v=1;v<w[i];v++) if(!used[v]) c++;
        r += c*fact[5-i];
        used[w[i]]=1;
    }
    return r;
}
static void unrankp(int r,int *w){
    int avail[6]={1,2,3,4,5,6}, n=6;
    for(int i=0;i<6;i++){
        int f=fact[n-1], k=r/f; r%=f;
        w[i]=avail[k];
        for(int j=k;j<n-1;j++) avail[j]=avail[j+1];
        n--;
    }
}

static void build(void){
    for(int i=0;i<NP;i++) unrankp(i,permw[i]);
    for(int i=0;i<NP;i++){
        int *p=permw[i], t[6];
        /* rho: p2p3p4p5p1p6 */
        t[0]=p[1];t[1]=p[2];t[2]=p[3];t[3]=p[4];t[4]=p[0];t[5]=p[5];
        rho_[i]=rankp(t);
        /* rot^{-1}: p6p1p2p3p4p5 */
        t[0]=p[5];t[1]=p[0];t[2]=p[1];t[3]=p[2];t[4]=p[3];t[5]=p[4];
        rotinv_[i]=rankp(t);
    }
    /* classes: canonical = min index over rot^i */
    for(int i=0;i<NP;i++) cls_[i]=-1;
    int nc=0;
    for(int i=0;i<NP;i++){
        if(cls_[i]>=0) continue;
        int q=i;
        do { cls_[q]=nc; /* rot(q) */
             int *p=permw[q],t[6];
             t[0]=p[1];t[1]=p[2];t[2]=p[3];t[3]=p[4];t[4]=p[5];t[5]=p[0];
             q=rankp(t);
        } while(q!=i);
        nc++;
    }
    if(nc!=NC){ fprintf(stderr,"class count %d != 120\n",nc); exit(1);}
    /* cost-3 successors: q starts with p4p5p6, then any perm of {p1,p2,p3} */
    static int p3[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
    for(int i=0;i<NP;i++){
        int *p=permw[i],t[6];
        for(int k=0;k<6;k++){
            t[0]=p[3];t[1]=p[4];t[2]=p[5];
            t[3]=p[p3[k][0]];t[4]=p[p3[k][1]];t[5]=p[p3[k][2]];
            succ3_[i][k]=rankp(t);
        }
    }
}

/* ---- self-check of d and out-degree profile ---- */
static int dcost(int i,int j){
    if(i==j) return 6;
    int *p=permw[i],*q=permw[j];
    for(int k=5;k>=1;k--){
        int ok=1;
        for(int t=0;t<k;t++) if(p[6-k+t]!=q[t]){ok=0;break;}
        if(ok) return 6-k;
    }
    return 6;
}
static void selfcheck(void){
    long prof[7]={0};
    for(int j=0;j<NP;j++) if(j!=0) prof[dcost(0,j)]++;
    printf("# out-degree profile from 123456: d1..d6 = %ld/%ld/%ld/%ld/%ld/%ld\n",
        prof[1],prof[2],prof[3],prof[4],prof[5],prof[6]);
    /* verify succ3 */
    for(int i=0;i<NP;i++){
        for(int k=0;k<6;k++) if(dcost(i,succ3_[i][k])!=3){fprintf(stderr,"succ3 bad\n");exit(1);}
    }
    /* rho order 5 */
    for(int i=0;i<NP;i++){
        int q=i; for(int k=0;k<5;k++) q=rho_[q];
        if(rho_[rho_[rho_[rho_[rho_[i]]]]]!=i){fprintf(stderr,"rho order\n");exit(1);}
    }
    /* the 5 classes C(rho^j x) distinct? report */
    int bad=0;
    for(int i=0;i<NP;i++){
        int c[5],q=i;
        for(int j=0;j<5;j++){c[j]=cls_[q];q=rho_[q];}
        for(int j=0;j<5;j++)for(int k=j+1;k<5;k++) if(c[j]==c[k]) bad++;
    }
    printf("# rho-orbit class collisions (over all 720 heads, pairs): %d\n",bad);
}

/* ---- result table ---- */
typedef struct {
    int8_t best[MAXCOST][2][2];
    int8_t wl[MAXCOST][2][2][40];   /* witness lengths */
    int    wh[MAXCOST][2][2][40];   /* witness heads   */
    unsigned long long nodes;
} Res;

typedef struct {
    Mask used;
    int  head;
    int  cost, blocks, run, a;
    int8_t lens[40];
    int    heads[40];
} St;

static void record(Res *R, int cost,int a,int b,int blocks, St *s){
    if(blocks > R->best[cost][a][b]){
        R->best[cost][a][b]=(int8_t)blocks;
        for(int i=0;i<blocks && i<40;i++){R->wl[cost][a][b][i]=s->lens[i];R->wh[cost][a][b][i]=s->heads[i];}
    }
}

static void dfs(St *s, Res *R){
    int cur = s->head;
    int marked[5], nm=0;
    for(int l=1;l<=5;l++){
        int c = cls_[cur];
        if(MGET(s->used,c)) break;
        MSET(s->used,c); marked[nm++]=c;
        int ncost = s->cost + (5-l);
        if(ncost <= CMAX){
            int rp = (l>=4) ? s->run+1 : 0;
            if(!USE_GATE || rp<=4){
                int nb = s->blocks+1;
                int aa = (s->blocks==0) ? (l<5) : s->a;
                int bb = (l<5);
                R->nodes++;
                if(nb<40){ s->lens[nb-1]=(int8_t)l; s->heads[nb-1]=s->head; }
                record(R,ncost,aa,bb,nb,s);
                int z = rotinv_[cur];
                int sc=s->cost, sb=s->blocks, sr=s->run, sa=s->a, sh=s->head;
                s->cost=ncost; s->blocks=nb; s->run=rp; s->a=aa;
                for(int k=0;k<6;k++){
                    s->head = succ3_[z][k];
                    dfs(s,R);
                }
                s->cost=sc; s->blocks=sb; s->run=sr; s->a=sa; s->head=sh;
            }
        }
        cur = rho_[cur];
    }
    for(int i=0;i<nm;i++) MCLR(s->used,marked[i]);
}

/* ---- parallel driver: split at a given depth ---- */
#define MAXTASK 4000000
static St *tasks; static int ntask=0;
static int SPLIT=3;

static void gen(St *s, Res *R, int depth){
    if(depth==SPLIT){ tasks[ntask++]=*s; return; }
    int cur=s->head; int marked[5],nm=0;
    for(int l=1;l<=5;l++){
        int c=cls_[cur];
        if(MGET(s->used,c)) break;
        MSET(s->used,c); marked[nm++]=c;
        int ncost=s->cost+(5-l);
        if(ncost<=CMAX){
            int rp=(l>=4)?s->run+1:0;
            if(!USE_GATE || rp<=4){
                int nb=s->blocks+1;
                int aa=(s->blocks==0)?(l<5):s->a;
                int bb=(l<5);
                R->nodes++;
                if(nb<40){s->lens[nb-1]=(int8_t)l;s->heads[nb-1]=s->head;}
                record(R,ncost,aa,bb,nb,s);
                int z=rotinv_[cur];
                int sc=s->cost,sb=s->blocks,sr=s->run,sa=s->a,sh=s->head;
                s->cost=ncost;s->blocks=nb;s->run=rp;s->a=aa;
                for(int k=0;k<6;k++){ s->head=succ3_[z][k]; gen(s,R,depth+1); }
                s->cost=sc;s->blocks=sb;s->run=sr;s->a=sa;s->head=sh;
            }
        }
        cur=rho_[cur];
    }
    for(int i=0;i<nm;i++) MCLR(s->used,marked[i]);
}

static int NT=1;
static volatile int next_task=0;
static pthread_mutex_t mu=PTHREAD_MUTEX_INITIALIZER;
static Res *tres;
static volatile int done_count=0;

static void *worker(void *arg){
    long id=(long)arg;
    Res *R=&tres[id];
    for(;;){
        pthread_mutex_lock(&mu);
        int t=next_task++;
        if(t%2000==0 && t<ntask) fprintf(stderr,"[task %d/%d]\n",t,ntask);
        pthread_mutex_unlock(&mu);
        if(t>=ntask) break;
        St s=tasks[t];
        dfs(&s,R);
    }
    return NULL;
}

int main(int argc,char**argv){
    for(int i=1;i<argc;i++){
        if(!strncmp(argv[i],"-c",2)) CMAX=atoi(argv[i]+2);
        else if(!strncmp(argv[i],"-t",2)) NT=atoi(argv[i]+2);
        else if(!strncmp(argv[i],"-s",2)) SPLIT=atoi(argv[i]+2);
        else if(!strncmp(argv[i],"-g",2)) USE_GATE=atoi(argv[i]+2);
    }
    build(); selfcheck();
    printf("# CMAX=%d threads=%d split=%d gate=%d\n",CMAX,NT,SPLIT,USE_GATE);
    fflush(stdout);
    tasks=malloc(sizeof(St)*MAXTASK);
    tres=calloc(NT+1,sizeof(Res));
    for(int c=0;c<MAXCOST;c++)for(int a=0;a<2;a++)for(int b=0;b<2;b++)
        for(int t=0;t<=NT;t++) tres[t].best[c][a][b]=-1;

    St s; memset(&s,0,sizeof(s));
    s.head=rankp((int[]){1,2,3,4,5,6});
    s.cost=0;s.blocks=0;s.run=0;s.a=0;
    struct timespec t0,t1; clock_gettime(CLOCK_MONOTONIC,&t0);
    gen(&s,&tres[NT],0);
    fprintf(stderr,"# generated %d tasks\n",ntask);
    pthread_t th[64];
    for(long i=0;i<NT;i++) pthread_create(&th[i],NULL,worker,(void*)i);
    for(long i=0;i<NT;i++) pthread_join(th[i],NULL);
    clock_gettime(CLOCK_MONOTONIC,&t1);
    double el=(t1.tv_sec-t0.tv_sec)+1e-9*(t1.tv_nsec-t0.tv_nsec);

    /* reduce */
    Res *G=calloc(1,sizeof(Res));
    for(int c=0;c<MAXCOST;c++)for(int a=0;a<2;a++)for(int b=0;b<2;b++) G->best[c][a][b]=-1;
    for(int t=0;t<=NT;t++){
        G->nodes += tres[t].nodes;
        for(int c=0;c<MAXCOST;c++)for(int a=0;a<2;a++)for(int b=0;b<2;b++)
            if(tres[t].best[c][a][b] > G->best[c][a][b]){
                G->best[c][a][b]=tres[t].best[c][a][b];
                memcpy(G->wl[c][a][b],tres[t].wl[c][a][b],40);
                memcpy(G->wh[c][a][b],tres[t].wh[c][a][b],40*sizeof(int));
            }
    }
    printf("# nodes=%llu  time=%.2fs  rate=%.2f Mnode/s\n",G->nodes,el,G->nodes/el/1e6);
    printf("cost  g(c,0,0) g(c,1,0) g(c,0,1) g(c,1,1)\n");
    for(int c=0;c<=CMAX;c++){
        printf("%d",c);
        int ord[4][2]={{0,0},{1,0},{0,1},{1,1}};
        for(int k=0;k<4;k++){
            int v=G->best[c][ord[k][0]][ord[k][1]];
            if(v<0) printf(" & --"); else printf(" & %d",v);
        }
        printf(" \\\\\n");
    }
    /* witnesses for top costs */
    for(int c=(CMAX>=2?CMAX-1:0);c<=CMAX;c++)
      for(int a=0;a<2;a++)for(int b=0;b<2;b++){
        int v=G->best[c][a][b]; if(v<0) continue;
        printf("W c=%d a=%d b=%d blocks=%d lens=",c,a,b,v);
        for(int i=0;i<v&&i<40;i++) printf("%d",G->wl[c][a][b][i]);
        printf(" heads=");
        for(int i=0;i<v&&i<40;i++){ int h=G->wh[c][a][b][i];
            for(int j=0;j<6;j++) printf("%d",permw[h][j]); printf(","); }
        printf("\n");
      }
    fflush(stdout);
    return 0;
}
