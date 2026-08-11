/* E012 -- negative b: x^3 - 3 b x - b^3, b <= -2.
   (a) field is imaginary cubic? (disc<0, irreducible)
   (b) is eps = theta-(b+1) the fundamental unit (up to sign)?  record power n
   (c) exceptions = SAME Pell D^2-3E^2=1, the two sign branches giving b<-1
   (d) extended Main Theorem: 3 nmid b, b^3-4 squarefree => eps fundamental
   gp gotcha on this build: keep each for(...) on ONE physical line. */

print("=== E012  negative b  x^3-3bx-b^3, b<=-2 ===");

\\ (a)(b) basic scan
print("\n(a)(b) b : disc_sign  irred  N(eps)  power_n  index");
scanrange(lo,hi) = for(b=lo,hi, if(b>=-1,next); f=x^3-3*b*x-b^3; ir=polisirreducible(f); d=poldisc(f); bnf=bnfinit(f); th=Mod(x,f); eps=th-(b+1); ne=norm(eps); ex=bnfisunit(bnf,eps); nn=abs(lift(ex[1])); idx=sqrtint((poldisc(f))/(bnf.disc)); printf("  b=%4d : dsgn=%2d ir=%d Neps=%2d n=%s idx=%d\n", b, sign(d), ir, ne, nn, idx));
scanrange(-30,-2);

\\ (b) exceptions by bnfisunit
print("\n(c) EXCEPTIONS (n>1) for b in [-5000,-2] via bnfisunit:");
findexc(lo,hi) = for(bb=lo,hi, b=-bb; f=x^3-3*b*x-b^3; bnf=bnfinit(f); th=Mod(x,f); eps=th-(b+1); ex=bnfisunit(bnf,eps); nn=abs(lift(ex[1])); if(nn>1, printf("  b=%5d  n=%d   |b|^3+4 = %d = %s\n", b, nn, (-b)^3+4, factor((-b)^3+4))));
findexc(2,5000);

\\ (c) Pell prediction:  b = 1 - A^2 + s*2(A+1)E ,  A in {D+1,1-D}, s=+-1,
\\     over Pell solutions D^2-3E^2=1 INCLUDING the trivial (D,E)=(1,0).
print("\n(c) Pell-predicted negative exceptions in [-5000,-2] (incl. trivial (1,0)):");
emit(D,E) = my(L=List()); for(j=1,2, A=if(j==1,D+1,1-D); for(si=0,1, s=2*si-1; b=1-A^2+s*2*(A+1)*E; if(b<-1 && b>=-5000, listput(L,b)))); Vec(L);
allneg=List(); D=1;E=0; bb=emit(D,E); for(i=1,#bb,listput(allneg,bb[i]));
D=2;E=1; for(k=1,12, bb=emit(D,E); for(i=1,#bb, listput(allneg,bb[i])); Dn=2*D+3*E; En=D+2*E; D=Dn; E=En);
print("  predicted: ", vecsort(Vec(allneg),,8));
print("  (b=-3 is the trivial-Pell E=0 member: A=2, b=1-4=-3; n=8 since |D_K|=31 tiny)");

\\ (d) extended Main Theorem confirmation
print("\n(d) Main Theorem (b<=-2, 3 nmid b, b^3-4 squarefree => eps fundamental):");
cnt=0; fail=0; failist=List();
chk(b)= f=x^3-3*b*x-b^3; bnf=bnfinit(f); eps=Mod(x,f)-(b+1); n=abs(lift(bnfisunit(bnf,eps)[1])); if(n!=1, fail++; listput(failist,[b,n])); cnt++;
for(c=2,2000, b=-c; if(c%3==0,next); if(!issquarefree(b^3-4),next); chk(b));
printf("  checked %d hypothesis-satisfying b in [-2000,-2]; failures = %d  %s\n", cnt, fail, Vec(failist));

\\ (d) size inequality for negative b:  27|b^3-4| > 4(3(b^2+b+1))^{3/2}+24
print("\n(d) size inequality 27|b^3-4| > 4(3(b^2+b+1))^{3/2}+24, c=|b|=2..40:");
sz=1; for(c=2,40, b=-c; L=27*abs(b^3-4); R=4.0*(3*(b^2+b+1))^(3/2)+24; if(L<=R, sz=0; printf("  FAIL c=%d\n",c))); print("  holds for all c=2..40: ", sz);

\\ (d) out-of-sample: k=4 negative Pell predictions beyond the -5000 scan
print("\n(d) out-of-sample bnfisunit on k=4 negative Pell predictions:");
oos(b)= f=x^3-3*b*x-b^3; bnf=bnfinit(f); eps=Mod(x,f)-(b+1); n=lift(bnfisunit(bnf,eps)[1]); printf("  b=%7d : n=%d  even(square)?=%d\n", b, n, abs(n)%2==0);
oos(-19855); oos(-20691);

print("\ndone E012");
