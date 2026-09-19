/* mysweep.c -- R-n6-7 reviewer's INDEPENDENT stage-2 engine, written from the
 * raw definitions of proof6.md sect.1 only.  No code from the artifact.
 *
 * MODE 0 (linear): the author's model M(census): q1's arc (or bq1 span) at
 *   123456; chains joined by exact d=3 hops; M2 closes in nested (linear)
 *   order; d4 jump/close moves; zh/zp3 B-joins for (15,0,1); cycle endgame.
 *   = independent re-execution of realize2/3/4.
 * MODE 1 (loops): the model WITHOUT lemmas R1/R1': the closure structure may
 *   contain loops (a chain closing its own component, or a cycle of
 *   components).  WLOG (relabelling) the FIRST loop's anchor piece sits at
 *   123456 and q1 is free over all 720 perms.  Loop content: arcs, d4 moves,
 *   inline M2/B joins; closes when a chain end reaches the anchor by the
 *   join move type of the anchor piece.  Up to 2 loops (>= #M2+B pieces
 *   bounds loop count); after the loops, the linear remainder from free q1.
 * A SAT here means the census is realizable in the R1-free model; UNSAT
 * EXHAUSTED means the census is empty even without assuming R1/R1'.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int rotT[720], rotiT[720], rhoT[720], clsT[720], H3[720][6], D4[720][24];
static int nH3[720], nD4[720];
static int orbT[720], opos[720], operm[144][5];
static int cmem[120][6], cn_[120];
static char P[720][7];
static int pid_lookup(const char*);

static char pstr[720][7];
static int npr = 0;
static void gen(char *buf, int used, int depth){
    if(depth == 6){ buf[6] = 0; strcpy(pstr[npr++], buf); return; }
    for(int c = 1; c <= 6; c++){
        if(used & (1 << c)) continue;
        buf[depth] = '0' + c;
        gen(buf, used | (1 << c), depth + 1);
    }
}
static int pid_lookup(const char *s){
    int lo = 0, hi = 719;
    while(lo <= hi){ int m = (lo + hi) / 2; int c = strcmp(pstr[m], s);
        if(c == 0) return m; if(c < 0) lo = m + 1; else hi = m - 1; }
    return -1;
}
static int rawd(const char *a, const char *b){
    for(int k = 1; k <= 6; k++){
        int ok = 1;
        for(int i = 0; i + k < 6; i++) if(a[i + k] != b[i]) { ok = 0; break; }
        if(ok) return k;
    }
    return 6;
}
static void init_tables(void){
    char buf[8]; gen(buf, 0, 0);
    for(int i = 0; i < 720; i++){
        char t[8];
        for(int j = 0; j < 6; j++) t[j] = pstr[i][(j + 1) % 6]; t[6] = 0;
        rotT[i] = pid_lookup(t);
        t[0] = pstr[i][5]; for(int j = 1; j < 6; j++) t[j] = pstr[i][j - 1]; t[6] = 0;
        rotiT[i] = pid_lookup(t);
        for(int j = 0; j < 4; j++) t[j] = pstr[i][j + 1];
        t[4] = pstr[i][0]; t[5] = pstr[i][5]; t[6] = 0;
        rhoT[i] = pid_lookup(t);
    }
    /* classes: canonical-min over rot */
    for(int i = 0; i < 720; i++) clsT[i] = -1;
    int nc = 0;
    for(int i = 0; i < 720; i++){
        if(clsT[i] >= 0) continue;
        int mn = i, q = i;
        for(int k = 0; k < 5; k++){ q = rotT[q]; if(q < mn) mn = q; }
        if(mn != i) continue;
        q = i; for(int k = 0; k < 6; k++){ clsT[q] = nc; q = rotT[q]; }
        nc++;
    }
    if(nc != 120){ fprintf(stderr, "class fail\n"); exit(9); }
    memset(cn_, 0, sizeof cn_);
    for(int i = 0; i < 720; i++) cmem[clsT[i]][cn_[clsT[i]]++] = i;
    /* rho orbits */
    int seen[720]; memset(seen, 0, sizeof seen); int no = 0;
    for(int i = 0; i < 720; i++){
        if(seen[i]) continue;
        int q = i;
        for(int j = 0; j < 5; j++){ orbT[q] = no; opos[q] = j; operm[no][j] = q; seen[q] = 1; q = rhoT[q]; }
        if(q != i){ fprintf(stderr, "orbit fail\n"); exit(9); }
        no++;
    }
    if(no != 144){ fprintf(stderr, "orbit count fail\n"); exit(9); }
    /* d=3 and d=4 successors from the raw definition */
    for(int i = 0; i < 720; i++){
        nH3[i] = nD4[i] = 0;
        for(int j = 0; j < 720; j++){
            int d = rawd(pstr[i], pstr[j]);
            if(d == 3) H3[i][nH3[i]++] = j;
            else if(d == 4) D4[i][nD4[i]++] = j;
        }
        if(nH3[i] != 6 || nD4[i] != 24){ fprintf(stderr, "succ fail\n"); exit(9); }
    }
}

/* ---- search state ---- */
static uint64_t cv0, cv1;
static uint8_t om[144];
static int rem[6], m2s[5], m2n, ncy, d4n, bn, bmode, blen, bq1;
static long long nodes, CAP = 200000000000LL;
static int satfound;
static long long n_closures, n_phaseQ, n_loop2;
static int trace[64][3], ntr = 0, wtr[64][3], wn = -1;
static void tpush(int k,int a,int b){ if(ntr<64){trace[ntr][0]=k;trace[ntr][1]=a;trace[ntr][2]=b;ntr++;} }
static void tpop(void){ if(ntr>0) ntr--; }
static int mode, loopbudget, chainonly;

static inline int cget(int c){ return c < 64 ? (int)((cv0 >> c) & 1) : (int)((cv1 >> (c - 64)) & 1); }
static inline void cset(int c){ if(c < 64) cv0 |= 1ULL << c; else cv1 |= 1ULL << (c - 64); }
static inline void cclr(int c){ if(c < 64) cv0 &= ~(1ULL << c); else cv1 &= ~(1ULL << (c - 64)); }

static int parc(int x, int l, int *u){
    int q = x;
    for(int j = 0; j < l; j++){
        if((om[orbT[q]] >> opos[q]) & 1 || cget(clsT[q])){
            for(int k = j - 1; k >= 0; k--){ om[orbT[u[k]]] &= ~(1 << opos[u[k]]); cclr(clsT[u[k]]); }
            return 0;
        }
        om[orbT[q]] |= 1 << opos[q]; cset(clsT[q]); u[j] = q; q = rhoT[q];
    }
    return 1;
}
static void uarc(int l, int *u){
    for(int k = l - 1; k >= 0; k--){ om[orbT[u[k]]] &= ~(1 << opos[u[k]]); cclr(clsT[u[k]]); }
}
static int pspan(int x, int l1, int l2, int *u){   /* K1 crits, nc, K2 crits */
    int span = l1 + 1 + l2, q = x;
    for(int j = 0; j < span; j++){
        int bad = (om[orbT[q]] >> opos[q]) & 1;
        if(!bad && j != l1 && cget(clsT[q])) bad = 1;
        if(bad){
            for(int k = j - 1; k >= 0; k--){ om[orbT[u[k]]] &= ~(1 << opos[u[k]]); if(k != l1) cclr(clsT[u[k]]); }
            return 0;
        }
        om[orbT[q]] |= 1 << opos[q]; if(j != l1) cset(clsT[q]); u[j] = q; q = rhoT[q];
    }
    return 1;
}
static void uspan(int l1, int l2, int *u){
    int span = l1 + 1 + l2;
    for(int k = span - 1; k >= 0; k--){ om[orbT[u[k]]] &= ~(1 << opos[u[k]]); if(k != l1) cclr(clsT[u[k]]); }
}
static int aend(int x, int l){ int q = x; for(int j = 1; j < l; j++) q = rhoT[q]; return rotiT[q]; }

static int eg(void){
    nodes++;
    if(nodes > CAP){ printf("CAPPED\n"); exit(3); }
    if(chainonly) return 1;
    if(ncy == 0) return cv0 == ~0ULL && cv1 == (1ULL << 56) - 1;
    int c = -1;
    for(int i = 0; i < 120; i++) if(!cget(i)){ c = i; break; }
    if(c < 0) return 0;
    for(int t = 0; t < 6; t++){
        int p = cmem[c][t], o = orbT[p], pc = opos[p];
        if(om[o]) continue;
        for(int ncp = 0; ncp < 5; ncp++){
            if(ncp == pc) continue;
            int ok = 1;
            for(int j = 0; j < 5; j++) if(j != ncp && cget(clsT[operm[o][j]])){ ok = 0; break; }
            if(!ok) continue;
            om[o] = 31; ncy--;
            for(int j = 0; j < 5; j++) if(j != ncp) cset(clsT[operm[o][j]]);
            if(eg()) return 1;
            for(int j = 0; j < 5; j++) if(j != ncp) cclr(clsT[operm[o][j]]);
            ncy++; om[o] = 0;
        }
    }
    return 0;
}

/* linear DFS (phase Q); also used inside loops via the same move set. */
static int anchor = -1, anchor_kind = 0, in_loop = 0;
static int phaseQ(void);        /* free-q1 linear phase (after loops) */
static int loop_dfs(int end);
static int lin(int end);

static int after_loop(void);
static int do_moves(int end, int (*rec)(int)){
    int u[8];
    /* hop moves */
    for(int t = 0; t < 6; t++){
        int x = H3[end][t];
        for(int l = 5; l >= 1; l--){
            if(!rem[l]) continue;
            if(!parc(x, l, u)) continue;
            rem[l]--;
            if(rec(aend(x, l))) return 1;
            rem[l]++; uarc(l, u);
        }
        if(m2n > (in_loop ? 0 : bq1)){
            for(int s2 = 2; s2 <= 4; s2++){
                if(!m2s[s2]) continue;
                for(int l1 = 1; l1 < s2; l1++){
                    int l2 = s2 - l1;
                    if(!pspan(x, l1, l2, u)) continue;
                    m2s[s2]--; m2n--;
                    int k2 = x; for(int j = 0; j <= l1; j++) k2 = rhoT[k2];
                    if(rec(aend(k2, l2))) return 1;
                    m2n++; m2s[s2]++; uspan(l1, l2, u);
                }
            }
        }
        if(bn && bmode == 1){        /* zh-close: x is the nc start */
            int q = x, ok = !((om[orbT[x]] >> opos[x]) & 1), w[8];
            if(ok){
                q = rhoT[x];
                for(int j = 0; j < blen; j++){
                    if((om[orbT[q]] >> opos[q]) & 1 || cget(clsT[q])){ ok = 0; break; }
                    w[j] = q; q = rhoT[q];
                }
            }
            if(ok){
                om[orbT[x]] |= 1 << opos[x];
                for(int j = 0; j < blen; j++){ om[orbT[w[j]]] |= 1 << opos[w[j]]; cset(clsT[w[j]]); }
                bn--;
                if(rec(aend(rhoT[x], blen))) return 1;
                bn++;
                for(int j = 0; j < blen; j++){ om[orbT[w[j]]] &= ~(1 << opos[w[j]]); cclr(clsT[w[j]]); }
                om[orbT[x]] &= ~(1 << opos[x]);
            }
        }
        if(bn && bmode == 2){        /* b2-close + zp3 launch */
            int q = x, ok = 1, w[8];
            for(int j = 0; j < blen; j++){
                if((om[orbT[q]] >> opos[q]) & 1 || cget(clsT[q])){ ok = 0; break; }
                w[j] = q; q = rhoT[q];
            }
            int ncp = q;
            if(ok && ((om[orbT[ncp]] >> opos[ncp]) & 1)) ok = 0;
            if(ok){
                for(int j = 0; j < blen; j++){ om[orbT[w[j]]] |= 1 << opos[w[j]]; cset(clsT[w[j]]); }
                om[orbT[ncp]] |= 1 << opos[ncp];
                bn--;
                int z = rotiT[ncp];
                /* the zp3-launched chain begins at a d3 successor of z */
                for(int h = 0; h < 6; h++){
                    int y = H3[z][h], u2[8];
                    if(in_loop && anchor_kind == 1 && y == anchor){
                        n_closures++;
                        int sv = in_loop; in_loop = 0;
                        if(after_loop()){ in_loop = sv; return 1; }
                        in_loop = sv;
                    }
                    for(int l = 5; l >= 1; l--){
                        if(!rem[l]) continue;
                        if(!parc(y, l, u2)) continue;
                        rem[l]--;
                        if(rec(aend(y, l))){ return 1; }
                        rem[l]++; uarc(l, u2);
                    }
                    if(m2n){    /* fused: zp3 lands on B1's closer head */
                        for(int s2 = 2; s2 <= 4; s2++){
                            if(!m2s[s2]) continue;
                            for(int l1 = 1; l1 < s2; l1++){
                                int l2 = s2 - l1, u3[8];
                                if(!pspan(y, l1, l2, u3)) continue;
                                m2s[s2]--; m2n--;
                                int k2 = y; for(int j = 0; j <= l1; j++) k2 = rhoT[k2];
                                if(rec(aend(k2, l2))) return 1;
                                m2n++; m2s[s2]++; uspan(l1, l2, u3);
                            }
                        }
                    }
                }
                bn++;
                om[orbT[ncp]] &= ~(1 << opos[ncp]);
                for(int j = blen - 1; j >= 0; j--){ om[orbT[w[j]]] &= ~(1 << opos[w[j]]); cclr(clsT[w[j]]); }
            }
        }
    }
    /* d4 moves */
    if(d4n){
        for(int t = 0; t < 24; t++){
            int x = D4[end][t];
            for(int l = 5; l >= 1; l--){
                if(!rem[l]) continue;
                if(!parc(x, l, u)) continue;
                rem[l]--; d4n--;
                if(rec(aend(x, l))) return 1;
                d4n++; rem[l]++; uarc(l, u);
            }
            if(m2n > (in_loop ? 0 : bq1)){
                for(int s2 = 2; s2 <= 4; s2++){
                    if(!m2s[s2]) continue;
                    for(int l1 = 1; l1 < s2; l1++){
                        int l2 = s2 - l1;
                        if(!pspan(x, l1, l2, u)) continue;
                        m2s[s2]--; m2n--; d4n--;
                        int k2 = x; for(int j = 0; j <= l1; j++) k2 = rhoT[k2];
                        if(rec(aend(k2, l2))) return 1;
                        d4n++; m2n++; m2s[s2]++; uspan(l1, l2, u);
                    }
                }
            }
        }
    }
    return 0;
}

static int lin(int end){
    nodes++;
    if(nodes > CAP){ printf("CAPPED\n"); exit(3); }
    if(m2n == 0 && d4n == 0 && bn == 0){
        int left = 0; for(int l = 1; l <= 5; l++) left += rem[l];
        if(left == 0) return eg();
    }
    return do_moves(end, lin);
}

/* ---- loop machinery ---- */
static int after_loop(void);
static int loop_dfs(int end){
    nodes++;
    if(nodes > CAP){ printf("CAPPED\n"); exit(3); }
    /* closure move: reach the anchor by its join type */
    if(anchor_kind == 1 || anchor_kind == 2 || anchor_kind == 4){
        /* span K1 head (1), zh nc (2), zp3 K head (4): entered by exact d3 */
        for(int t = 0; t < 6; t++) if(H3[end][t] == anchor){
            n_closures++;
            int sv = in_loop; in_loop = 0;
            if(after_loop()){ in_loop = sv; return 1; }
            in_loop = sv;
        }
        if(anchor_kind == 1 && d4n){    /* d4-close onto the anchored span */
            for(int t = 0; t < 24; t++) if(D4[end][t] == anchor){
                n_closures++;
                d4n--;
                int sv = in_loop; in_loop = 0;
                if(after_loop()){ in_loop = sv; d4n++; return 1; }
                in_loop = sv; d4n++;
            }
        }
    }
    return do_moves(end, loop_dfs);
}

static int start_loop(int x, int kind, int lb2);
static int loops_left;

static int after_loop(void){
    /* optionally start a second loop with a free anchor, else phase Q */
    if(loops_left > 0 && (m2n > bq1 || bn)){
        loops_left--;
        for(int x = 0; x < 720; x++){
            if(m2n > bq1){
                for(int s2 = 2; s2 <= 4; s2++){
                    if(!m2s[s2]) continue;
                    for(int l1 = 1; l1 < s2; l1++)
                        if(start_loop(x, 1, l1 * 10 + (s2 - l1))){ loops_left++; return 1; }
                }
            }
            if(bn) if(start_loop(x, bmode == 1 ? 2 : 4, blen)){ loops_left++; return 1; }
        }
        loops_left++;
    }
    return phaseQ();
}

static int start_loop(int x, int kind, int arg){
    int u[8];
    int sa = anchor, sk = anchor_kind, sl = in_loop;
    anchor = x; in_loop = 1;
    int r = 0;
    if(kind == 1){
        int l1 = arg / 10, l2 = arg % 10, s2 = l1 + l2;
        anchor_kind = 1;
        if(m2s[s2] && pspan(x, l1, l2, u)){
            m2s[s2]--; m2n--;
            int k2 = x; for(int j = 0; j <= l1; j++) k2 = rhoT[k2];
            r = loop_dfs(aend(k2, l2));
            if(!r){ m2n++; m2s[s2]++; uspan(l1, l2, u); }
        }
    } else if(kind == 2){    /* zh B: anchor is the nc start */
        anchor_kind = 2;
        int ok = !((om[orbT[x]] >> opos[x]) & 1), w[8], q = rhoT[x];
        for(int j = 0; ok && j < arg; j++){
            if((om[orbT[q]] >> opos[q]) & 1 || cget(clsT[q])) ok = 0;
            else { w[j] = q; q = rhoT[q]; }
        }
        if(ok){
            om[orbT[x]] |= 1 << opos[x];
            for(int j = 0; j < arg; j++){ om[orbT[w[j]]] |= 1 << opos[w[j]]; cset(clsT[w[j]]); }
            bn--;
            r = loop_dfs(aend(rhoT[x], arg));
            if(!r){
                bn++;
                for(int j = 0; j < arg; j++){ om[orbT[w[j]]] &= ~(1 << opos[w[j]]); cclr(clsT[w[j]]); }
                om[orbT[x]] &= ~(1 << opos[x]);
            }
        }
    } else if(kind == 4){    /* zp3 B2: anchor is K's head; launch from z */
        anchor_kind = 4;
        int ok = 1, w[8], q = x;
        for(int j = 0; ok && j < arg; j++){
            if((om[orbT[q]] >> opos[q]) & 1 || cget(clsT[q])) ok = 0;
            else { w[j] = q; q = rhoT[q]; }
        }
        int ncp = q;
        if(ok && ((om[orbT[ncp]] >> opos[ncp]) & 1)) ok = 0;
        if(ok){
            for(int j = 0; j < arg; j++){ om[orbT[w[j]]] |= 1 << opos[w[j]]; cset(clsT[w[j]]); }
            om[orbT[ncp]] |= 1 << opos[ncp];
            bn--;
            int z = rotiT[ncp];
            for(int h = 0; h < 6 && !r; h++){
                int y = H3[z][h], u2[8];
                if(y == x){
                    /* immediate self-launch: the zp3 lands on B2's own K head */
                    n_closures++;
                    int sv = in_loop; in_loop = 0;
                    if(after_loop()) r = 1;
                    in_loop = sv;
                }
                for(int l = 5; l >= 1 && !r; l--){
                    if(!rem[l]) continue;
                    if(!parc(y, l, u2)) continue;
                    rem[l]--;
                    r = loop_dfs(aend(y, l));
                    if(!r){ rem[l]++; uarc(l, u2); }
                }
                if(!r && m2n){    /* fused: zp3 lands on B1's closer head */
                    for(int s2 = 2; s2 <= 4 && !r; s2++){
                        if(!m2s[s2]) continue;
                        for(int l1 = 1; l1 < s2 && !r; l1++){
                            int l2 = s2 - l1, u3[8];
                            if(!pspan(y, l1, l2, u3)) continue;
                            m2s[s2]--; m2n--;
                            int k2 = y; for(int j = 0; j <= l1; j++) k2 = rhoT[k2];
                            r = loop_dfs(aend(k2, l2));
                            if(!r){ m2n++; m2s[s2]++; uspan(l1, l2, u3); }
                        }
                    }
                }
            }
            if(!r){
                bn++;
                om[orbT[ncp]] &= ~(1 << opos[ncp]);
                for(int j = arg - 1; j >= 0; j--){ om[orbT[w[j]]] &= ~(1 << opos[w[j]]); cclr(clsT[w[j]]); }
            }
        }
    }
    if(!r){ anchor = sa; anchor_kind = sk; in_loop = sl; }
    return r;
}

static int q1free;
static int phaseQ(void){
    n_phaseQ++;
    int u[8];
    int lo = q1free ? 0 : pid_lookup("123456");
    int hi = q1free ? 719 : lo;
    for(int q = lo; q <= hi; q++){
        if(!bq1){
            for(int l = 5; l >= 1; l--){
                if(!rem[l]) continue;
                if(!parc(q, l, u)) continue;
                rem[l]--;
                if(lin(aend(q, l))){ rem[l]++; uarc(l, u); return 1; }
                rem[l]++; uarc(l, u);
            }
        } else {
            for(int s2 = 2; s2 <= 4; s2++){
                if(!m2s[s2]) continue;
                for(int l1 = 1; l1 < s2; l1++){
                    int l2 = s2 - l1;
                    if(!pspan(q, l1, l2, u)) continue;
                    m2s[s2]--; m2n--;
                    int sb = bq1; bq1 = 0;
                    int k2 = q; for(int j = 0; j <= l1; j++) k2 = rhoT[k2];
                    int r = lin(aend(k2, l2));
                    bq1 = sb; m2n++; m2s[s2]++; uspan(l1, l2, u);
                    if(r) return 1;
                }
            }
        }
    }
    return 0;
}

int main(int argc, char **argv){
    init_tables();
    if(argc < 12){
        printf("usage: mysweep n5 n4 n3 n2 n1 ncyc s2list bq1 nd4 bmode blen [mode] [cap]\n");
        return 1;
    }
    rem[5] = atoi(argv[1]); rem[4] = atoi(argv[2]); rem[3] = atoi(argv[3]);
    rem[2] = atoi(argv[4]); rem[1] = atoi(argv[5]);
    ncy = atoi(argv[6]);
    memset(m2s, 0, sizeof m2s); m2n = 0;
    if(strcmp(argv[7], "0")){
        char *tok = strtok(argv[7], ",");
        while(tok){ m2s[atoi(tok)]++; m2n++; tok = strtok(NULL, ","); }
    }
    bq1 = atoi(argv[8]); d4n = atoi(argv[9]);
    bmode = atoi(argv[10]); blen = atoi(argv[11]);
    bn = bmode ? 1 : 0;
    mode = argc > 12 ? atoi(argv[12]) : 0;
    if(getenv("CHAINONLY")) chainonly = 1;
    if(argc > 13) CAP = atoll(argv[13]);
    /* E-9: instance consistency.  The piece multiset must cover the 120
       rotation classes EXACTLY -- 5n5+4n4+3n3+2n2+n1 for the one-block
       components, 4 per type-I cycle, the span totals, and the defect piece.
       Without this an argv that is shifted or mis-encoded is answered with a
       confident "UNSAT ... EXHAUSTED" for an instance nobody asked about.
       The clean-room engine has had this check since it was written
       (n6c11_decide.c: `tot != 120` -> rc=3). */
    {
        int tot = 5*rem[5] + 4*rem[4] + 3*rem[3] + 2*rem[2] + 1*rem[1]
                  + 4*ncy + blen;
        for(int v = 2; v <= 4; v++) tot += v * m2s[v];
        if(tot != 120){
            printf("INSTFAIL tot=%d != 120 "
                   "(5n5+4n4+3n3+2n2+n1 + 4*ncyc + sum(s2) + blen)\n", tot);
            return 3;
        }
    }
    int sat = 0;
    if(mode == 0){
        q1free = 0; in_loop = 0; loops_left = 0;
        sat = phaseQ();
    } else {
        /* loop mode: anchor first loop at 123456, q1 free; up to 2 loops */
        q1free = 1; loops_left = (m2n - bq1 + bn >= 2) ? 1 : 0;
        int a0 = pid_lookup("123456");
        if(m2n > bq1){
            for(int s2 = 2; s2 <= 4 && !sat; s2++){
                if(!m2s[s2]) continue;
                for(int l1 = 1; l1 < s2 && !sat; l1++)
                    sat = start_loop(a0, 1, l1 * 10 + (s2 - l1));
            }
        }
        if(!sat && bn) sat = start_loop(a0, bmode == 1 ? 2 : 4, blen);
    }
    printf("%s nodes=%lld closures=%lld phaseQ=%lld EXHAUSTED\n", sat ? "SAT" : "UNSAT", nodes, n_closures, n_phaseQ);
    return sat ? 0 : 2;
}
