/* C6-A independent check: over the abstract-chain domain (head 123456 and,
 * as a stronger check, ALL 720 heads), every chain all of whose link-paths
 * have length in {4,5} has at most 4 paths, at most 2 of length 4, and no
 * length-4 path in an interior position.  No cap, no cost bound, no pruning. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define NP 720
#define NC 120
static int permw[NP][6]; static int rho_[NP],rotinv_[NP],cls_[NP],succ3_[NP][6];
static int fact[7]={1,1,2,6,24,120,720};
static int rankp(const int*w){int u[7]={0},r=0;for(int i=0;i<6;i++){int c=0;for(int v=1;v<w[i];v++)if(!u[v])c++;r+=c*fact[5-i];u[w[i]]=1;}return r;}
static void unrankp(int r,int*w){int a[6]={1,2,3,4,5,6},n=6;for(int i=0;i<6;i++){int f=fact[n-1],k=r/f;r%=f;w[i]=a[k];for(int j=k;j<n-1;j++)a[j]=a[j+1];n--;}}
static void build(void){
  for(int i=0;i<NP;i++)unrankp(i,permw[i]);
  for(int i=0;i<NP;i++){int*p=permw[i],t[6];
    t[0]=p[1];t[1]=p[2];t[2]=p[3];t[3]=p[4];t[4]=p[0];t[5]=p[5];rho_[i]=rankp(t);
    t[0]=p[5];t[1]=p[0];t[2]=p[1];t[3]=p[2];t[4]=p[3];t[5]=p[4];rotinv_[i]=rankp(t);}
  for(int i=0;i<NP;i++)cls_[i]=-1; int nc=0;
  for(int i=0;i<NP;i++){if(cls_[i]>=0)continue;int q=i;
    do{cls_[q]=nc;int*p=permw[q],t[6];t[0]=p[1];t[1]=p[2];t[2]=p[3];t[3]=p[4];t[4]=p[5];t[5]=p[0];q=rankp(t);}while(q!=i);nc++;}
  static int p3[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
  for(int i=0;i<NP;i++){int*p=permw[i],t[6];
    for(int k=0;k<6;k++){t[0]=p[3];t[1]=p[4];t[2]=p[5];t[3]=p[p3[k][0]];t[4]=p[p3[k][1]];t[5]=p[p3[k][2]];succ3_[i][k]=rankp(t);}}
}
static uint64_t used[2];
#define G(c) ((used[(c)>>6]>>((c)&63))&1ULL)
#define S(c) (used[(c)>>6]|=1ULL<<((c)&63))
#define K(c) (used[(c)>>6]&=~(1ULL<<((c)&63)))
static int maxpaths=0,maxfour=0,interior4=0;
static int lens[64];
static void dfs(int x,int depth){
  int cur=x,marked[5],nm=0;
  /* need classes for lengths 1..3 marked before we can place a length-4/5 path */
  for(int l=1;l<=5;l++){
    int c=cls_[cur]; if(G(c))break; S(c);marked[nm++]=c;
    if(l>=4){
      lens[depth]=l; int nd=depth+1;
      if(nd>maxpaths)maxpaths=nd;
      int f=0; for(int i=0;i<nd;i++) if(lens[i]==4)f++;
      if(f>maxfour)maxfour=f;
      for(int i=1;i<nd-1;i++) if(lens[i]==4) interior4++;
      int z=rotinv_[cur];
      for(int k=0;k<6;k++) dfs(succ3_[z][k],nd);
    }
    cur=rho_[cur];
  }
  for(int i=0;i<nm;i++)K(marked[i]);
}
int main(void){
  build();
  used[0]=used[1]=0;
  int h0=rankp((int[]){1,2,3,4,5,6});
  dfs(h0,0);
  printf("head 123456: max paths=%d max len4=%d interior-4 occurrences=%d\n",maxpaths,maxfour,interior4);
  maxpaths=maxfour=interior4=0;
  for(int h=0;h<NP;h++){ used[0]=used[1]=0; dfs(h,0); }
  printf("all 720 heads: max paths=%d max len4=%d interior-4 occurrences=%d\n",maxpaths,maxfour,interior4);
  return 0;
}
