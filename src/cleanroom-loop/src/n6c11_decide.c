/* n6c11_decide -- clean-room re-implementation of Algorithm alg:sweep
 * ("Loop-complete class elimination"), Appendix A.6 of PAPER-n6-872-v2.tex.
 *
 * Written from the paper's printed specification alone (definitions of
 * rot/sig/rho, rotation classes, runs, critical permutations, link-paths,
 * hops, the geometric model of Section sec:search, Lemma lem:closure, and
 * the pseudocode of Algorithm alg:sweep).  No other implementation was
 * consulted.
 *
 * Usage:
 *   n6c11_decide --tag NAME --mode 0|1 --n5 a --n4 b --n3 c --n2 d --n1 e
 *                --c1 k --spans 2,3 --bq1 0|1 --x4h h [--defect zh:2|zp3:3]
 *                [--cap N] [--weaken hop|heavy]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

/* ------------------------------------------------------------------ tables */
static int NP = 720;
static unsigned char word[720][6];
static int rotv[720], rotinv[720], rhov[720], rhoinv[720];
static int clsv[720];              /* rotation class id 0..119 */
static int orbrep[720];            /* representative index of the rho-orbit */
static int orbmem[144][5];         /* members of each orbit, in rho order    */
static int orbid[720], orbpos[720];
static int succ3[720][6], succ4[720][24];
static int classmem[120][6];       /* the six permutations of each class     */

static int idx_of(const unsigned char *w)
{
    int i, j, r = 0, f = 120;
    unsigned char avail[7] = {0, 1, 1, 1, 1, 1, 1};
    for (i = 0; i < 6; i++) {
        int c = 0;
        for (j = 1; j < w[i]; j++) c += avail[j];
        r += c * f;
        avail[w[i]] = 0;
        if (5 - i > 0) f /= (5 - i);
    }
    return r;
}

static void build(void)
{
    int i, j, k, p[6], used[7];
    /* enumerate the 720 words in lexicographic order */
    int n = 0;
    unsigned char w[6];
    int a, b, c, d, e, f;
    for (a = 1; a <= 6; a++) for (b = 1; b <= 6; b++) { if (b == a) continue;
      for (c = 1; c <= 6; c++) { if (c == a || c == b) continue;
        for (d = 1; d <= 6; d++) { if (d == a || d == b || d == c) continue;
          for (e = 1; e <= 6; e++) { if (e == a || e == b || e == c || e == d) continue;
            for (f = 1; f <= 6; f++) { if (f == a || f == b || f == c || f == d || f == e) continue;
              word[n][0]=a; word[n][1]=b; word[n][2]=c; word[n][3]=d;
              word[n][4]=e; word[n][5]=f; n++; } } } } }
    if (n != 720) { fprintf(stderr, "perm build failed\n"); exit(2); }
    (void)i; (void)j; (void)k; (void)p; (void)used; (void)w;

    for (i = 0; i < 720; i++) {
        unsigned char t[6];
        /* rot(p) = p2p3p4p5p6p1 */
        for (j = 0; j < 5; j++) t[j] = word[i][j + 1];
        t[5] = word[i][0];
        rotv[i] = idx_of(t);
        /* rho(p) = p2p3p4p5p1p6 */
        for (j = 0; j < 4; j++) t[j] = word[i][j + 1];
        t[4] = word[i][0]; t[5] = word[i][5];
        rhov[i] = idx_of(t);
    }
    for (i = 0; i < 720; i++) { rotinv[rotv[i]] = i; rhoinv[rhov[i]] = i; }

    /* rotation classes */
    for (i = 0; i < 720; i++) clsv[i] = -1;
    { int nc = 0;
      for (i = 0; i < 720; i++) if (clsv[i] < 0) {
          int q = i, m;
          for (m = 0; m < 6; m++) { clsv[q] = nc; classmem[nc][m] = q; q = rotv[q]; }
          if (q != i) { fprintf(stderr, "rot order != 6\n"); exit(2); }
          nc++;
      }
      if (nc != 120) { fprintf(stderr, "classes=%d\n", nc); exit(2); }
    }
    /* rho-orbits */
    for (i = 0; i < 720; i++) orbid[i] = -1;
    { int no = 0;
      for (i = 0; i < 720; i++) if (orbid[i] < 0) {
          int q = i, m;
          for (m = 0; m < 5; m++) { orbid[q] = no; orbpos[q] = m; orbmem[no][m] = q; q = rhov[q]; }
          if (q != i) { fprintf(stderr, "rho order != 5\n"); exit(2); }
          orbrep[i] = i; no++;
      }
      if (no != 144) { fprintf(stderr, "orbits=%d\n", no); exit(2); }
    }
    /* the 5 positions of an orbit lie in 5 distinct classes (checked) */
    for (i = 0; i < 144; i++) {
        int s = 0, m1, m2;
        for (m1 = 0; m1 < 5; m1++) for (m2 = m1 + 1; m2 < 5; m2++)
            if (clsv[orbmem[i][m1]] == clsv[orbmem[i][m2]]) s++;
        if (s) { fprintf(stderr, "orbit %d has repeated class\n", i); exit(2); }
    }
    /* cost-3 successors: q = p4p5p6 + a permutation of (p1,p2,p3)  (6)
       cost-4 successors: q = p5p6   + a permutation of (p1,p2,p3,p4) (24) */
    for (i = 0; i < 720; i++) {
        unsigned char t[6];
        int r3 = 0, r4 = 0;
        int P3[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
        static int P4[24][4]; static int built4 = 0;
        if (!built4) {
            int x1,x2,x3,x4,m=0;
            for (x1=0;x1<4;x1++) for (x2=0;x2<4;x2++) { if(x2==x1) continue;
              for (x3=0;x3<4;x3++) { if(x3==x1||x3==x2) continue;
                for (x4=0;x4<4;x4++) { if(x4==x1||x4==x2||x4==x3) continue;
                  P4[m][0]=x1;P4[m][1]=x2;P4[m][2]=x3;P4[m][3]=x4;m++; } } }
            built4 = 1;
        }
        for (j = 0; j < 6; j++) {
            t[0]=word[i][3]; t[1]=word[i][4]; t[2]=word[i][5];
            t[3]=word[i][P3[j][0]]; t[4]=word[i][P3[j][1]]; t[5]=word[i][P3[j][2]];
            succ3[i][r3++] = idx_of(t);
        }
        for (j = 0; j < 24; j++) {
            t[0]=word[i][4]; t[1]=word[i][5];
            t[2]=word[i][P4[j][0]]; t[3]=word[i][P4[j][1]];
            t[4]=word[i][P4[j][2]]; t[5]=word[i][P4[j][3]];
            succ4[i][r4++] = idx_of(t);
        }
    }
}

/* ------------------------------------------------------------------- state */
static uint64_t occ[12];      /* occupied rho-positions (= permutations) */
static uint64_t cov[2];       /* covered rotation classes                */
static int rem[6];            /* one-block pieces (arcs) by path length  */
static int spanc[5];          /* two-block pieces by total path length   */
static int cyc;               /* remaining type-I cycles                 */
static int heavy;             /* remaining cost->=4 join budget          */
static int def_kind = -1;     /* 0 = zh, 1 = zp3, -1 = none              */
static int def_lB;
static int def_left;          /* 1 while the defect piece is unplaced    */
static int bq1;
static int weaken_hop = 0, weaken_heavy = 0;

static unsigned long long nodes = 0, cap_nodes = 0;
static int capped = 0, sat = 0;
static int nclosures = 0;             /* closure events taken (fingerprint) */
static unsigned long long closcount = 0;

#define OCC(p)   ((occ[(p)>>6] >> ((p)&63)) & 1ULL)
#define SETO(p)  (occ[(p)>>6] |=  (1ULL << ((p)&63)))
#define CLRO(p)  (occ[(p)>>6] &= ~(1ULL << ((p)&63)))
#define COV(c)   ((cov[(c)>>6] >> ((c)&63)) & 1ULL)
#define SETC(c)  (cov[(c)>>6] |=  (1ULL << ((c)&63)))
#define CLRC(c)  (cov[(c)>>6] &= ~(1ULL << ((c)&63)))

/* place `len` consecutive critical positions from x; classes covered.
   returns 1 on success, 0 on failure (nothing left placed). */
static int place_block(int x, int len, int *cells)
{
    int k, p = x;
    for (k = 0; k < len; k++) {
        if (OCC(p) || COV(clsv[p])) {
            int m; for (m = 0; m < k; m++) { CLRO(cells[m]); CLRC(clsv[cells[m]]); }
            return 0;
        }
        SETO(p); SETC(clsv[p]); cells[k] = p; p = rhov[p];
    }
    return 1;
}
static void unplace_block(int *cells, int len)
{
    int k; for (k = 0; k < len; k++) { CLRO(cells[k]); CLRC(clsv[cells[k]]); }
}

/* a piece is a run of consecutive rho-positions from x; `gap` is the index
   of the single non-critical position, or -1 for none. */
static int place_piece(int x, int len, int gap, int *cells)
{
    int k, p = x;
    for (k = 0; k < len; k++) {
        if (OCC(p) || (k != gap && COV(clsv[p]))) {
            int m; for (m = 0; m < k; m++) { CLRO(cells[m]);
                                             if (m != gap) CLRC(clsv[cells[m]]); }
            return 0;
        }
        SETO(p); if (k != gap) SETC(clsv[p]);
        cells[k] = p; p = rhov[p];
    }
    return 1;
}
static void unplace_piece(int *cells, int len, int gap)
{
    int k; for (k = 0; k < len; k++) { CLRO(cells[k]);
                                       if (k != gap) CLRC(clsv[cells[k]]); }
}

static int all_consumed(void)
{
    int i;
    for (i = 1; i <= 5; i++) if (rem[i]) return 0;
    for (i = 2; i <= 4; i++) if (spanc[i]) return 0;
    if (def_left) return 0;
    if (heavy) return 0;
    return 1;
}

/* --------------------------------------------------------------- endgame */
static int endgame(void)
{
    int c, m, s;
    if (cap_nodes && nodes >= cap_nodes) { capped = 1; return 0; }
    nodes++;
    if (cyc == 0) {
        for (c = 0; c < 120; c++) if (!COV(c)) return 0;
        return 1;
    }
    for (c = 0; c < 120; c++) if (!COV(c)) break;
    if (c == 120) return 0;                      /* cycles left, nothing to cover */
    for (m = 0; m < 6; m++) {
        int p = classmem[c][m], o = orbid[p], k, ok = 1;
        for (k = 0; k < 5; k++) if (OCC(orbmem[o][k])) { ok = 0; break; }
        if (!ok) continue;
        for (s = 0; s < 5; s++) {                /* s = the non-critical slot */
            int cells[5];
            if (orbmem[o][s] == p) continue;     /* class c must be covered   */
            if (!place_piece(orbmem[o][0], 5, s, cells)) continue;
            cyc--;
            if (endgame()) { cyc++; unplace_piece(cells, 5, s); return 1; }
            cyc++;
            unplace_piece(cells, 5, s);
            if (capped) return 0;
        }
    }
    return 0;
}

/* ---------------------------------------------------------------- walkers */
static int lin(int end);
static int loopwalk(int end, int anchor, int nloops);
static int after_loop(int nloops);

/* one piece placed from head position x; returns exit permutation via *xit */
/* Moves(end, R): R selected by `mode` (0 linear, 1 loop). */
static int moves(int end, int mode, int anchor, int nloops)
{
    int hi, i, l, s, l1, l2, cells[5];
    int heavy_pass;
    for (heavy_pass = 0; heavy_pass < 2; heavy_pass++) {
        int nsucc;
        if (heavy_pass == 0) nsucc = weaken_hop ? 720 : 6;
        else { if (heavy <= 0) break; nsucc = weaken_heavy ? 720 : 24; }
        for (i = 0; i < nsucc; i++) {
            int x;
            if (heavy_pass == 0) x = weaken_hop ? i : succ3[end][i];
            else                 x = weaken_heavy ? i : succ4[end][i];
            if (heavy_pass == 1) heavy--;
            /* --- arcs --- */
            for (l = 1; l <= 5; l++) if (rem[l]) {
                if (!place_block(x, l, cells)) continue;
                rem[l]--;
                { int xit = rotinv[cells[l - 1]];
                  int r = (mode == 0) ? lin(xit) : loopwalk(xit, anchor, nloops);
                  rem[l]++; unplace_block(cells, l);
                  if (r) { if (heavy_pass == 1) heavy++; return 1; }
                  if (capped) { if (heavy_pass == 1) heavy++; return 0; } }
            }
            /* --- spans --- */
            for (s = 2; s <= 4; s++) if (spanc[s]) {
                for (l1 = 1; l1 < s; l1++) {
                    l2 = s - l1;
                    if (!place_piece(x, l1 + 1 + l2, l1, cells)) continue;
                    spanc[s]--;
                    { int xit = rotinv[cells[l1 + l2]];
                      int r = (mode == 0) ? lin(xit) : loopwalk(xit, anchor, nloops);
                      spanc[s]++; unplace_piece(cells, l1 + 1 + l2, l1);
                      if (r) { if (heavy_pass == 1) heavy++; return 1; }
                      if (capped) { if (heavy_pass == 1) heavy++; return 0; } }
                }
            }
            /* --- defect piece --- */
            if (def_left) {
                int len = def_lB + 1, gap = (def_kind == 0) ? 0 : def_lB;
                if (place_piece(x, len, gap, cells)) {
                    def_left = 0;
                    { int xit = rotinv[cells[len - 1]];
                      int r = (mode == 0) ? lin(xit) : loopwalk(xit, anchor, nloops);
                      def_left = 1; unplace_piece(cells, len, gap);
                      if (r) { if (heavy_pass == 1) heavy++; return 1; }
                      if (capped) { if (heavy_pass == 1) heavy++; return 0; } }
                }
            }
            if (heavy_pass == 1) heavy++;
        }
    }
    (void)hi;
    return 0;
}

static int lin(int end)
{
    if (cap_nodes && nodes >= cap_nodes) { capped = 1; return 0; }
    nodes++;
    if (all_consumed()) return endgame();
    return moves(end, 0, 0, 0);
}

/* place the piece that starts the linear remainder at head position y */
static int lin_start_at(int y)
{
    int cells[5], l, s, l1, l2;
    if (bq1) {
        for (s = 2; s <= 4; s++) if (spanc[s]) for (l1 = 1; l1 < s; l1++) {
            l2 = s - l1;
            if (!place_piece(y, l1 + 1 + l2, l1, cells)) continue;
            spanc[s]--;
            { int r = lin(rotinv[cells[l1 + l2]]);
              spanc[s]++; unplace_piece(cells, l1 + 1 + l2, l1);
              if (r) return 1; if (capped) return 0; }
        }
    } else {
        for (l = 1; l <= 5; l++) if (rem[l]) {
            if (!place_block(y, l, cells)) continue;
            rem[l]--;
            { int r = lin(rotinv[cells[l - 1]]);
              rem[l]++; unplace_block(cells, l);
              if (r) return 1; if (capped) return 0; }
        }
    }
    return 0;
}

/* the linear remainder, with q1 free over all 720 positions */
static int linear_free(void)
{
    int y;
    if (cap_nodes && nodes >= cap_nodes) { capped = 1; return 0; }
    nodes++;
    if (all_consumed()) return endgame();
    for (y = 0; y < 720; y++) {
        if (OCC(y)) continue;
        if (lin_start_at(y)) return 1;
        if (capped) return 0;
    }
    return 0;
}

/* anchor a loop-capable piece at head position y and walk its loop */
static int anchor_loop_at(int y, int nloops)
{
    int cells[5], s, l1, l2;
    for (s = 2; s <= 4; s++) if (spanc[s]) for (l1 = 1; l1 < s; l1++) {
        l2 = s - l1;
        if (!place_piece(y, l1 + 1 + l2, l1, cells)) continue;
        spanc[s]--;
        { int r = loopwalk(rotinv[cells[l1 + l2]], y, nloops);
          spanc[s]++; unplace_piece(cells, l1 + 1 + l2, l1);
          if (r) return 1; if (capped) return 0; }
    }
    if (def_left) {
        int len = def_lB + 1, gap = (def_kind == 0) ? 0 : def_lB;
        if (place_piece(y, len, gap, cells)) {
            def_left = 0;
            { int r = loopwalk(rotinv[cells[len - 1]], y, nloops);
              def_left = 1; unplace_piece(cells, len, gap);
              if (r) return 1; if (capped) return 0; }
        }
    }
    return 0;
}

static int loop_pieces_left(void)
{
    int s, n = 0;
    for (s = 2; s <= 4; s++) n += spanc[s];
    return n + def_left;
}

/* after a loop has closed: optionally anchor a second loop, then run the
   linear remainder with q1 free (Lemma lem:closure: at most two loops). */
static int after_loop(int nloops)
{
    int y;
    if (cap_nodes && nodes >= cap_nodes) { capped = 1; return 0; }
    nodes++;
    if (nloops < 2 && loop_pieces_left() > 0) {
        for (y = 0; y < 720; y++) {
            if (OCC(y)) continue;
            if (anchor_loop_at(y, nloops + 1)) return 1;
            if (capped) return 0;
        }
    }
    return linear_free();
}

static int loopwalk(int end, int anchor, int nloops)
{
    int i;
    if (cap_nodes && nodes >= cap_nodes) { capped = 1; return 0; }
    nodes++;
    /* closure: the current chain end reaches the anchor by the anchored
       piece's own entry type (cost-3 hop, or a cost->=4 join). */
    for (i = 0; i < 6; i++) if (succ3[end][i] == anchor) {
        closcount++;
        if (after_loop(nloops)) return 1;
        if (capped) return 0;
        break;
    }
    if (heavy > 0) for (i = 0; i < 24; i++) if (succ4[end][i] == anchor) {
        heavy--; closcount++;
        { int r = after_loop(nloops); heavy++;
          if (r) return 1; if (capped) return 0; }
        break;
    }
    return moves(end, 1, anchor, nloops);
}

/* ------------------------------------------------------------------- main */
int main(int argc, char **argv)
{
    int i, mode = 0;
    const char *tag = "run";
    int n[6]; memset(n, 0, sizeof n);
    memset(spanc, 0, sizeof spanc);
    cyc = 0; heavy = 0; bq1 = 0; def_left = 0;

    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--tag")) tag = argv[++i];
        else if (!strcmp(argv[i], "--mode")) mode = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--n5")) n[5] = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--n4")) n[4] = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--n3")) n[3] = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--n2")) n[2] = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--n1")) n[1] = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--c1")) cyc = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--bq1")) bq1 = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--x4h")) heavy = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--cap")) cap_nodes = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "--weaken")) {
            const char *w = argv[++i];
            if (!strcmp(w, "hop")) weaken_hop = 1;
            else if (!strcmp(w, "heavy")) weaken_heavy = 1;
        }
        else if (!strcmp(argv[i], "--spans")) {
            char *s = argv[++i], *t;
            if (strcmp(s, "-")) for (t = strtok(s, ","); t; t = strtok(0, ","))
                spanc[atoi(t)]++;
        }
        else if (!strcmp(argv[i], "--defect")) {
            char *s = argv[++i];
            if (strcmp(s, "none")) {
                def_kind = (s[1] == 'h') ? 0 : 1;
                def_lB = atoi(strchr(s, ':') + 1);
                def_left = 1;
            }
        }
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    for (i = 1; i <= 5; i++) rem[i] = n[i];
    build();

    /* sanity: the piece multiset must cover exactly the 120 classes */
    { int tot = 0;
      for (i = 1; i <= 5; i++) tot += i * rem[i];
      for (i = 2; i <= 4; i++) tot += i * spanc[i];
      tot += 4 * cyc;
      if (def_left) tot += def_lB;
      if (tot != 120) {
          fprintf(stderr, "%s: class total %d != 120\n", tag, tot); return 3; }
    }

    { clock_t t0 = clock();
      if (mode == 0) {
          sat = lin_start_at(0);          /* q1 = 123456, normalized */
      } else {
          sat = anchor_loop_at(0, 1);     /* one loop-capable piece anchored */
      }
      { double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
        const char *verdict = sat ? "SAT" : (capped ? "CAPPED" : "UNSAT EXHAUSTED");
        printf("%s mode=%d nodes=%llu closures=%llu %s time=%.1fs\n",
               tag, mode, nodes, closcount, verdict, secs);
        fflush(stdout);
        return sat ? 1 : (capped ? 4 : 0); }
    }
}
