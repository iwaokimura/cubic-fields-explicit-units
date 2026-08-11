\\ E016: biquadratic F_b and 3-class field tower (Kaneko 2014 §3 analogue) -- VERIFICATION
\\ Subfamily: v_3(b) even >=2  AND  b^3-4 squarefree  (forces b odd).
\\ Claim (for the theorem): eta=-1/eps_b is the fundamental unit, 3=p1 p2^2,
\\   no prime totally ramified, eta ≡ 1 (mod p1^2 p2^3); infinitely many such b.
default(parisize, "1G");

Pc(b) = 3*(b^2+b+1);
Qc(b) = 3*(b+1);
Ac(b) = -Pc(b);
Bc(b) = Qc(b);
fb(b) = x^3 - 3*b*x - b^3;
eta_of(b) = lift( Mod((b+1)-x, fb(b))^(-1) );

\\ ----- (1) congruence 27|A+3, 3^5|A+B  <=>  v_3(b) >= 2  (algebraic identity) -----
cong_ok(b) = ((Ac(b)+3)%27==0) && ((Ac(b)+Bc(b))%243==0);
print("(1) congruence  27|A+3 & 3^5|A+B  vs  v_3(b)>=2 :");
{ my(bad=0); for(m=1,4000, if(m%3!=0 && m%2==1, my(b=9*m); if(cong_ok(b)!=(valuation(b,3)>=2), bad++))); \
  for(m=1,4000, my(b=m); if(b>=3 && cong_ok(b)!=(valuation(b,3)>=2), bad++)); \
  print("    mismatches over b<=4000 (all b) and subfamily: ", bad); }

\\ ----- (2) algebraic: A+3 = -3b(b+1), A+B = -3b^2 -----
print("(2) identities A+3 == -3b(b+1), A+B == -3b^2 :");
{ my(bad=0); for(b=3,5000, if(Ac(b)+3 != -3*b*(b+1), bad++); if(Ac(b)+Bc(b) != -3*b^2, bad++)); print("    mismatches: ", bad); }

\\ ----- (3) index bound a^2 <= 9 b^3  and  |D_K| >= 3(b^3-4) on the subfamily -----
print("(3) subfamily {9|b, v3(b) even, b^3-4 squarefree}: a^2<=9b^3, |D_K|>=3(b^3-4), eta fundamental, 3=p1p2^2, no total ram, eta≡1 mod p1^2p2^3 :");
{ my(cnt=0, badA=0, badD=0, badfund=0, baddec=0, badtot=0, badcong=0, badq=0); \
  for(m=1, 260, if(m%2==1 && m%3!=0, \
    my(b=9*m); \
    if(valuation(b,3)%2==0 && issquarefree(b^3-4), \
      cnt++; \
      my(f=fb(b), nf=nfinit(f), dK=nf.disc, aa=sqrtint((-poldisc(f))\(-dK)) ); \
      if(aa^2 > 9*b^3, badA++); \
      if(abs(dK) < 3*(b^3-4), badD++); \
      my(bnf=bnfinit(f), eta=eta_of(b), u=bnfisunit(bnf, Mod(eta,f)) ); \
      if(abs(u[1])!=1, badfund++); \
      my(dec=idealprimedec(nf,3)); \
      if(#dec!=2 || vecsort([dec[1].e,dec[2].e])!=[1,2], baddec++); \
      my(fa=factor(abs(dK))[,1], tot=0); \
      for(i=1,#fa, my(dc=idealprimedec(nf,fa[i])); if(#dc==1 && dc[1].e==3, tot=1)); \
      if(tot, badtot++); \
      if(!cong_ok(b), badcong++); \
      my(p1,p2); if(dec[1].e==1, p1=dec[1];p2=dec[2], p1=dec[2];p2=dec[1]); \
      if(nfeltval(nf,eta-1,p1)<2 || nfeltval(nf,eta-1,p2)<3, badq++); \
    ))); \
  print("    subfamily count (b=9m<=2340, m odd 3∤m, b^3-4 sqfree): ", cnt); \
  print("    a^2>9b^3 : ", badA, " | |D_K|<3(b^3-4) : ", badD, " | eta not fundamental : ", badfund); \
  print("    3 != p1p2^2 : ", baddec, " | some prime totally ramified : ", badtot); \
  print("    congruence fails : ", badcong, " | eta !≡ 1 mod p1^2p2^3 : ", badq); }

\\ ----- (4) cube-exclusion inequality 3(b^3-4) > 12(b^2+b+1)+24 for b>=6 -----
print("(4) size inequality 3(b^3-4) > 12(b^2+b+1)+24 :");
{ my(bad=0, firstok=0); for(b=1,100, if(3*(b^3-4) > 12*(b^2+b+1)+24, if(firstok==0,firstok=b), if(b>=6,bad++))); \
  print("    smallest b with inequality: ", firstok, " ; failures at b>=6: ", bad); }

\\ ----- (5) 3-rank of Cl(F_b), F_b=Q(sqrt(-3),sqrt(b(b^3-4))) on small subfamily -----
print("(5) 3-rank of Cl(F_b) on small subfamily (supporting Kaneko's remark rank>1):");
{ for(m=1,20, if(m%2==1 && m%3!=0, my(b=9*m); \
    if(valuation(b,3)%2==0 && issquarefree(b^3-4), \
      my(g=polcompositum(x^2+3, x^2-b*(b^3-4))[1], bnf=bnfinit(g), cyc=bnf.clgp[2]); \
      my(r3=sum(i=1,#cyc, if(cyc[i]%3==0,1,0))); \
      print("    b=", b, "  Cl(F_b)=", cyc, "  3-rank=", r3)))); }

\\ ----- (6) infinitude density: squarefree b^3-4 among b=9m (m odd, 3∤m) -----
print("(6) infinitude: count b=9m<=X (m odd,3∤m) with b^3-4 squarefree :");
{ for(e=2,4, my(X=9*10^e, tot=0, sf=0); \
    for(m=1, 10^e, if(m%2==1 && m%3!=0, my(b=9*m); tot++; if(issquarefree(b^3-4), sf++))); \
    print("    X=", X, " : candidates ", tot, ", squarefree ", sf, "  (ratio ", sf*1.0/tot, ")")); }
quit;
