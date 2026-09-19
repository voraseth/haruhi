/* Independent superpermutation verifier for n=6. Usage: ./verify6 file.txt
 * Accepts digits 1-6; whitespace ignored; any other char is an error.
 * Exit 0 iff all 720 permutations occur as contiguous 6-windows. */
#include <stdio.h>
#include <string.h>
static char s[4000000];
static unsigned char seen[46656]; /* 6^6 */
int main(int argc, char **argv) {
    FILE *f = (argc > 1) ? fopen(argv[1], "r") : stdin;
    if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 2; }
    int L = 0, c;
    while ((c = fgetc(f)) != EOF) {
        if (c >= '1' && c <= '6') {
            if (L >= (int)sizeof(s)) { fprintf(stderr, "too long\n"); return 2; }
            s[L++] = (char)(c - '0');
        } else if (c=='\n'||c=='\r'||c==' '||c=='\t') continue;
        else { fprintf(stderr, "bad char 0x%02x at digit %d\n", c, L); return 2; }
    }
    memset(seen, 0, sizeof seen);
    int count = 0;
    for (int i = 0; i + 6 <= L; i++) {
        int mask = 0, idx = 0, ok = 1;
        for (int j = 0; j < 6; j++) {
            int d = s[i+j] - 1;
            if (mask >> d & 1) { ok = 0; break; }
            mask |= 1 << d; idx = idx * 6 + d;
        }
        if (ok && !seen[idx]) { seen[idx] = 1; count++; }
    }
    printf("length=%d distinct_perms=%d %s\n", L, count,
           count == 720 ? "VALID_SUPERPERM6" : "NOT_SUPERPERM6");
    return count == 720 ? 0 : 1;
}
