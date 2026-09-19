/* perm6.h  —  n=6 permutation utilities, written from raw definitions.
 * S-n6-build.  No code imported from other approaches. */
#ifndef PERM6_H
#define PERM6_H
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NP 720
#define NC 120

static unsigned char P[NP][6];      /* perms in lexicographic order, digits 1..6 */
static int PIDX[46656];             /* base-6 code of digits-1  ->  perm index, -1 if not a perm */
static unsigned char DIST[NP][NP];  /* d(p,q) = 6 - longest suffix of p that is a prefix of q */
static int ROT[NP];                 /* rot(p) = p2..p6 p1 */
static int CLS[NP];                 /* rotation class id 0..119 */
static int PHASE[NP];               /* p = rot^PHASE[p] ( rep of its class ) */
static int CREP[NC];                /* class rep = the rotation starting with digit 1 */
static int CMEM[NC][6];             /* CMEM[c][j] = rot^j(rep_c) */

static int code6(const unsigned char *a){int v=0;for(int i=0;i<6;i++)v=v*6+(a[i]-1);return v;}

static int dcalc(const unsigned char *p,const unsigned char *q){
    for(int k=1;k<=5;k++){            /* try overlap of 6-k letters */
        int ok=1;
        for(int i=0;i<6-k;i++) if(p[i+k]!=q[i]){ok=0;break;}
        if(ok) return k;
    }
    return 6;
}

static void perm6_init(void){
    unsigned char a[6]={1,2,3,4,5,6};
    int idx=0;
    /* lexicographic generation */
    for(int i=0;i<46656;i++) PIDX[i]=-1;
    while(1){
        memcpy(P[idx],a,6); PIDX[code6(a)]=idx; idx++;
        int i=4; while(i>=0 && a[i]>=a[i+1]) i--;
        if(i<0) break;
        int j=5; while(a[j]<=a[i]) j--;
        unsigned char t=a[i];a[i]=a[j];a[j]=t;
        for(int l=i+1,r=5;l<r;l++,r--){t=a[l];a[l]=a[r];a[r]=t;}
    }
    if(idx!=NP){fprintf(stderr,"perm gen failed %d\n",idx);exit(2);}
    for(int p=0;p<NP;p++){
        unsigned char b[6];
        for(int i=0;i<5;i++) b[i]=P[p][i+1];
        b[5]=P[p][0];
        ROT[p]=PIDX[code6(b)];
    }
    for(int p=0;p<NP;p++) for(int q=0;q<NP;q++) DIST[p][q]=(unsigned char)dcalc(P[p],P[q]);
    /* classes: rep = the unique rotation whose first digit is 1 */
    int nc=0;
    for(int p=0;p<NP;p++) CLS[p]=-1;
    for(int p=0;p<NP;p++){
        if(P[p][0]!=1) continue;
        int c=nc++;
        CREP[c]=p;
        int x=p;
        for(int j=0;j<6;j++){ CLS[x]=c; PHASE[x]=j; CMEM[c][j]=x; x=ROT[x]; }
        if(x!=p){fprintf(stderr,"rot order != 6\n");exit(2);}
    }
    if(nc!=NC){fprintf(stderr,"class count %d\n",nc);exit(2);}
    for(int p=0;p<NP;p++) if(CLS[p]<0){fprintf(stderr,"unclassed\n");exit(2);}
}
#endif
