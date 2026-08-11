/* E009 -- Closed form for the Pell exception family b_pm(k).
   l_n + f_n*sqrt3 = (2+sqrt3)^n ; l_n,f_n both satisfy u_{n+1}=4u_n-u_{n-1}.
   (l_0,l_1)=(1,2) -> 1,2,7,26,97,362,1351,...  (f_0,f_1)=(0,1) -> 0,1,4,15,56,209,780,...
   CLAIM (Thm. 5.2 of the paper, proved there by the Binet identities):
                                              b_pm(k)=(f_{2k-1}-1)/2 +- 2 f_{k-1};
   equivalently  b_+ + b_- = f_{2k-1}-1,  b_+ - b_- = 4 f_{k-1}. */

L=vector(40); FF=vector(40); L[1]=1; L[2]=2; FF[1]=0; FF[2]=1;
for(n=3,40, L[n]=4*L[n-1]-L[n-2]; FF[n]=4*FF[n-1]-FF[n-2]);
lof(n) = L[n+1];
fof(n) = FF[n+1];
bp(k) = (fof(2*k-1)-1)/2 + 2*fof(k-1);
bm(k) = (fof(2*k-1)-1)/2 - 2*fof(k-1);

\\ (1) Binet identities underpinning the closed form (must all print 0):
print("=== (1) Lucas/Binet identities (max abs error over k=1..18, must be 0) ===");
e1=0; e2=0; e3=0; e4=0;
for(k=1,18, e1=max(e1,abs(fof(2*k)-2*fof(k)*lof(k))); e2=max(e2,abs(3*fof(k)^2-(lof(2*k)-1)/2)); e3=max(e3,abs(2*fof(2*k)-lof(2*k)-fof(2*k-1))); e4=max(e4,abs(2*fof(k)-lof(k)-fof(k-1))));
printf("  f_{2k}=2f_k l_k:%d  3f_k^2=(l_{2k}-1)/2:%d  2f_{2k}-l_{2k}=f_{2k-1}:%d  2f_k-l_k=f_{k-1}:%d\n", e1,e2,e3,e4);

\\ (2) closed form vs ground-truth table (E003) and the E003 branch formula
print("\n=== (2) closed form vs E003 table & branch formula b=1-A^2+2|A+1|E ===");
truth=[[5,9],[96,112],[1425,1485],[20160,20384],[281941,282777]];
okT=1; okB=1;
for(k=2,6, my(D=lof(k),E=fof(k),bP=1-(D+1)^2+2*(D+2)*E,bM=1-(1-D)^2+2*abs(2-D)*E,t=truth[k-1]); if(!(bm(k)==t[1]&&bp(k)==t[2]),okT=0); if(!(bm(k)==bM&&bp(k)==bP),okB=0));
printf("  closed form == E003 table (k=2..6): %d ;  == E003 branch formula: %d\n", okT, okB);

\\ (3) sum/difference identities and the split recurrences
print("\n=== (3) b_++b_-=f_{2k-1}-1, b_+-b_-=4f_{k-1}; s_k=14s_{k-1}-s_{k-2}+12, d_k=4d_{k-1}-d_{k-2} ===");
sd=1; rc=1;
for(k=2,18, if(bp(k)+bm(k)!=fof(2*k-1)-1,sd=0); if(bp(k)-bm(k)!=4*fof(k-1),sd=0));
for(k=4,18, if((fof(2*k-1)-1)!=14*(fof(2*k-3)-1)-(fof(2*k-5)-1)+12,rc=0); if(4*fof(k-1)!=4*(4*fof(k-2))-4*fof(k-3),rc=0));
printf("  sum/diff identities (k=2..18): %d ;  split recurrences (k=4..18): %d\n", sd, rc);

\\ (4) table + out-of-sample bnfisunit confirmation (k=7)
print("\n=== (4) values + bnfisunit out-of-sample check ===");
for(k=2,9, printf("  k=%d: b_-=%d  b_+=%d\n", k, bm(k), bp(k)));
print("  bnfisunit at k=7 (exponent on fund. unit even => eps NOT fundamental):");
for(s=0,1, my(b=if(s==0,bm(7),bp(7)),f=x^3-3*b*x-b^3,BK=bnfinit(f,1),ex=bnfisunit(BK,Mod(x-(b+1),f))); printf("    b=%d (%s): exps=%s  n=%d even=%d\n", b, if(s==0,"b-","b+"), ex, abs(ex[1]), abs(ex[1])%2==0));
quit
