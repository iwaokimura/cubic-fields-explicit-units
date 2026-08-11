\\ check-paper-audit.gp --- E018: rigor re-audit of the submission draft.
\\ Each numbered block below re-checks one statement of the paper.
\\ gp gotcha: keep each for(...) and each name(args)=... on ONE physical line.
default(realprecision, 80);

print("################ A1/A2. exception scan: order n of eta, |b| <= NMAX ################");
NMAX = 3000;
for(b=-NMAX, NMAX, if(b>=2 || b<=-1, my(f=x^3-3*b*x-b^3); if(polisirreducible(f), my(K=bnfinit(f,1), eta=1/((b+1)-Mod(x,f)), n=abs(lift(bnfisunit(K,eta)[1]))); if(n!=1, print("b=",b," n=",n," D_K=",K.disc," sqfree(b^3-4)=",issquarefree(b^3-4)," 3|b=",b%3==0)))));
print("EXPECT: b=3 has n=13 (ODD => eta not a square: counterexample to `fails <=> square')");
print("EXPECT: b=-3 has n=8 (square) but b^3-4=-31 IS squarefree (counterexample to thm:exc)");

print();
print("################ B1. range of validity: b=-1 and b=2 are legitimate ################");
for(b=-2, 3, my(f=x^3-3*b*x-b^3); print("b=",b," disc=",poldisc(f)," irred=",polisirreducible(f)," #real roots=",if(polisirreducible(f),polsturm(f),-1)));
print("EXPECT: only b=0 (reducible) and b=1 (3 real roots) are excluded; abstract's `b<>2' is wrong");

print();
print("################ B2. Prop setup(iii): b<theta<b+1, eps in (-1,0) for ALL valid b ################");
bad=0; for(b=-200, 200, if(b>=2 || b<=-1, my(r=polrootsreal(x^3-3*b*x-b^3)[1]); if(!(r>b && r<b+1), bad++; print(" FAIL b=",b))));
print("failures (|b|<=200, both signs): ",bad,"   [one-line proof f(b)=-3b^2<0<1=f(b+1) is sign-free]");

print();
print("################ A4. eta < 3(b^2+b+1) is FALSE for b<=-2; eta < P+1 is uniform ################");
for(i=1,8, my(bb=[-100,-20,-7,-2,2,7,20,100][i], P=3*(bb^2+bb+1), e=polrootsreal(x^3-P*x^2+3*(bb+1)*x-1)[1]); print("b=",bb," eta=",e," P=",P," eta<P: ",e<P," eta<P+1: ",e<P+1));
P = 3*(b^2+b+1); Q = 3*(b+1);
print("h(P+1) - (P+1)*(3*(b+1)^2+4) + 1 = ", subst(x^3-P*x^2+Q*x-1, x, P+1) - ((P+1)*(3*(b+1)^2+4)-1), "   [so h(P+1)>0 always]");
print("h(1) = ", subst(x^3-P*x^2+Q*x-1, x, 1), "   [= -3b^2 < 0, so eta>1]");

print();
print("################ A4'. size inequality restated with P+1 ################");
Rpos = (27*b^3-132)^2 - 16*(3*b^2+3*b+4)^3;
print("R_+(b) = (27b^3-132)^2-16(3b^2+3b+4)^3 = ",Rpos);
print("  real roots = ",polrootsreal(Rpos),"  => 27(b^3-4) > 4(P+1)^{3/2}+24 for b>=7");
Rneg = (27*c^3+84)^2 - 16*(3*c^2-3*c+4)^3;
print("R_-(c) = (27c^3+84)^2-16(3c^2-3c+4)^3 = ",Rneg);
print("  real roots = ",polrootsreal(Rneg),"  => holds for ALL c>=2 (no finite check needed)");

print();
print("################ A5. Voronoi normal form fails exactly when b is NOT squarefree ################");
hast(b) = my(f,a,ok); f = x^3-3*b*x-b^3; a = sqrtint(abs(poldisc(f))\abs(nfdisc(f))); ok = 0; for(t=0, a^2-1, if((3*(t^2-b))%a==0 && (t^3-3*b*t-b^3)%(a^2)==0, ok=1; break)); return([a,ok]);
for(b=2, 200, if(b%3!=0 && issquarefree(b^3-4), my(r=hast(b)); if(r[2] != issquarefree(b), print(" b=",b," a=",r[1]," b squarefree=",issquarefree(b)," Voronoi t exists=",r[2]))));
print("(no output above => `t exists' <=> `b squarefree' throughout the range)");
for(i=1,3, my(b=[25,49,121][i], p=[5,7,11][i]); print(" b=",b,": nfbasis=",nfbasis(x^3-3*b*x-b^3),"   theta/",p," is integral => {1,theta,*} cannot be a basis"));

print();
print("################ A5'. b squarefree: t=0 always works, basis {1,theta,(theta^2-3b)/b} ################");
bad=0; cnt=0;
for(b=2, 400, if(b%3!=0 && issquarefree(b) && issquarefree(b^3-4), my(f=x^3-3*b*x-b^3, nf=nfinit(f)); cnt++; if(denominator(nfalgtobasis(nf,lift(Mod((x^2-3*b)/b,f))))!=1 || nfdisc(f)!=poldisc(f)/b^2, bad++; print(" FAIL b=",b))));
for(b=-400,-2, if(b%3!=0 && issquarefree(b) && issquarefree(b^3-4), my(f=x^3-3*b*x-b^3, nf=nfinit(f)); cnt++; if(denominator(nfalgtobasis(nf,lift(Mod((x^2-3*b)/b,f))))!=1 || nfdisc(f)!=poldisc(f)/b^2, bad++; print(" FAIL b=",b))));
print("tested ",cnt," b (|b|<=400, both signs); failures: ",bad);

print();
print("################ A6. Voronoi's quoted 3-adic condition 3 | n+q-1 = b^3+3b-1 ################");
for(b=4, 12, print(" b=",b," b mod 3=",b%3," (b^3+3b-1) mod 3=",(b^3+3*b-1)%3," Voronoi t exists=",hast(b)[2]));
print("=> the quoted condition fails exactly for b=1 mod 3 -- the very class used in thm:inf --");
print("   yet the basis is fine there (b=7,13,...): the quoted hypothesis is not the real one.");

print();
print("################ C1. ramification of 3 and 2 (intro claim is wrong) ################");
dec(b,p) = my(nf=nfinit(x^3-3*b*x-b^3), pd=idealprimedec(nf,p)); return([vector(#pd,i,[pd[i].e,pd[i].f]), valuation(nf.disc,p)]);
for(i=1,10, my(b=[2,4,5,7,-2,-4,3,9,27,-9][i], r=dec(b,3)); print(" p=3, b=",b," v_3(b)=",valuation(b,3)," b mod 3=",b%3," [e,f]=",r[1]," v_3(D_K)=",r[2]));
print("  => 3 !| b  :  3 is TOTALLY and WILDLY ramified (v_3(D_K)=4 if b=1, 3 if b=2 mod 3)");
print("  => 3 |  b  :  v_3(b) even -> p1 p2^2 (tame);  v_3(b) odd -> unramified");
for(i=1,8, my(b=[2,4,8,12,16,20,28,-12][i], r=dec(b,2)); print(" p=2, b=",b," w=",valuation(b,2)," b'=",b/2^valuation(b,2)," [e,f]=",r[1]," v_2(D_K)=",r[2]));
print("  => 2 ramifies (always wildly, e=p=2, as p1 p2^2) iff w odd, or w even & b'=1 mod 4");

print();
print("################ index formula v_p(a): full check ################");
vpa(b,p) = if(p>=5, if(b%p==0, floor(3*valuation(b,p)/2), floor(valuation(b^3-4,p)/2)), if(p==3, if(b%3!=0, 0, floor(3*(valuation(b,3)+1)/2)), my(w); if(b%2!=0, 0, w=valuation(b,2); if(w%2==1, (3*w-1)/2, 3*w/2 + if((b/2^w)%4==3,1,0)))));
bad = 0;
for(b=-400, 400, if(b>=2 || b<=-1, my(f=x^3-3*b*x-b^3, a=sqrtint(abs(poldisc(f))\abs(nfdisc(f))), ps=Set(concat(factor(b)~[1,], factor(b^3-4)~[1,])), pred=1); for(i=1,#ps, if(ps[i]>1, pred *= ps[i]^vpa(b,ps[i]))); if(pred != a, bad++; print(" MISMATCH b=",b," a=",a," pred=",pred))));
print("Thm idxprime+idx23 mismatches (|b|<=400, both signs): ", bad);

print();
print("################ A3. the four Pell branches: m vs m_b, and m^2/|b|^3 ################");
lucD(k) = round(real(((2+sqrt(3))^k+(2-sqrt(3))^k)/2));
pelE(k) = round(real(((2+sqrt(3))^k-(2-sqrt(3))^k)/(2*sqrt(3))));
dat(sA,s,k) = my(D=lucD(k), Ev=pelE(k), A, b, B, m, mb, pr); A = 1+sA*D; b = 1-A^2+s*2*(A+1)*Ev; B = (A^2-3*b-3)/2; m = abs(A*B-1); mb = 1; pr = 1; if(b!=0, my(fb=factor(abs(b))); for(i=1,#fb~, mb *= fb[i,1]^valuation(m,fb[i,1]); pr *= 1.*fb[i,1]^(2*valuation(m,fb[i,1])-3*valuation(b,fb[i,1])))); return([A,b,B,m,mb,pr]);
print("-- positive branches (m^2/(3b^3) -> 6.464): the proof of thm:exc has room --");
for(k=2, 8, my(r=dat(1,1,k), q=dat(-1,-1,k)); print(" k=",k," b_+=",r[2]," m^2/(3b^3)=",1.*r[4]^2/(3*r[2]^3),"   b_-=",q[2]," m^2/(3b^3)=",1.*q[4]^2/(3*q[2]^3)));
print("-- negative branches (m^2/(3|b|^3) -> 0.464 < 1): the proof BREAKS --");
for(k=0, 10, my(r=dat(1,-1,k)); if(r[2]<=-2, print(" k=",k," b=",r[2]," m=",r[4]," m_b=",r[5]," m>m_b=",r[4]>r[5]," m^2/|b|^3=",1.*r[4]^2/abs(r[2])^3," prod p^e_p=",r[6]," sqfree(b^3-4)=",issquarefree(r[2]^3-4))));
for(k=1, 10, my(r=dat(-1,1,k)); if(r[2]<=-2, print(" k=",k," b=",r[2]," m=",r[4]," m_b=",r[5]," m>m_b=",r[4]>r[5]," m^2/|b|^3=",1.*r[4]^2/abs(r[2])^3," prod p^e_p=",r[6]," sqfree(b^3-4)=",issquarefree(r[2]^3-4))));
print("=> b=-3 (E=0) is the EQUALITY case m=m_b, prod=3: the genuine counterexample.");
print("=> for b<0 one needs the sharp m_b^2 <= |b|^3 (old conj:mb, [E]), not m_b^2 <= 3|b|^3.");

print();
print("################ C2/A3. symbolic certificates for all four branches ################");
mul(u,v) = [u[1]*v[1] + (3*E^2+1)*u[2]*v[2], u[1]*v[2]+u[2]*v[1]];
cube(u) = mul(u,mul(u,u));
branch(sA, s) = my(A, A2, b, Bv, mv); A = [1, sA]; A2 = [3*E^2+2, 2*sA]; b = [-3*E^2-1+4*s*E, -2*sA + 2*s*sA*E]; Bv = [(A2[1]-3*b[1]-3)/2, (A2[2]-3*b[2])/2]; mv = mul(A,Bv); mv = [mv[1]-1, mv[2]]; return([b, Bv, mv, mul(mv,mv), cube(b)]);
show(sA,s,tag,lam) = my(r=branch(sA,s), m2=r[4], b3=r[5], res, R); res = [m2[1]+lam*b3[1], m2[2]+lam*b3[2]]; R = res[1]^2-(3*E^2+1)*res[2]^2; print("--- ",tag); print("    b = ",r[1][1]," + D*(",r[1][2],")"); print("    m = ",r[3][1]," + D*(",r[3][2],")"); print("    P0 = ",res[1]); print("    P1 = ",res[2]); print("    P0 real roots = ",polrootsreal(res[1])); print("    R = P0^2-(3E^2+1)P1^2 = ",factor(R));
print("== m^2-3b^3 on the two POSITIVE branches (lem:msize; fills the paper's FIXME for b_+) ==");
show(1,1,"b_+ = 9,112,1485,... (A=D+1, s=+1)",-3)
show(-1,-1,"b_- = 5,96,1425,... (A=1-D, s=-1)",-3)
print("== m^2-|b|^3 on the two NEGATIVE branches (what a fixed proof would need) ==");
show(1,-1,"b = -3,-16,-135,-1568,... (A=D+1, s=-1)",1)
show(-1,1,"b = -75,-1344,... (A=1-D, s=+1)",1)

print();
print("################ lem:mAB check on all four branches ################");
for(k=2, 6, for(i=1,4, my(sA=[1,-1,1,-1][i], s=[1,-1,-1,1][i], r=dat(sA,s,k), A=r[1], b=r[2], B=r[3], m=r[4]); print(" k=",k," b=",b," m=|AB-1|=",m==abs(A*B-1)," disc(f_b)=m^2 disc(eta_0): ",poldisc(x^3-3*b*x-b^3)==m^2*poldisc(x^3-B*x^2+A*x-1))));

print();
print("################ B3. thmA:exc closed form with k in Z reproduces the negatives ################");
ff(n) = round(real(((2+sqrt(3))^n-(2-sqrt(3))^n)/(2*sqrt(3))));
for(k=-5, 6, print(" k=",k," b_+=",(ff(2*k-1)-1)/2+2*ff(k-1)," b_-=",(ff(2*k-1)-1)/2-2*ff(k-1)));
print("=> k in Z is correct, but b_-(0)=1, b_-(-1)=b_+(1)=b_-(1)=0 are degenerate and must be excluded.");

print();
print("################ Artin's lemma: the symbolic identities ################");
F = 4*s^4 + 24*s^2 - 4*(1-c^2)*(s^2-2*s*c+1)^2;
G = 2*c*s^2 + 4*(1-c^2)*s + 2*c;
print("F - (G^2+16c^2s^2-4) = ", F - (G^2 + 16*c^2*s^2 - 4));
print("psi'(g) - 4(g-1)(g+2)^2 = ", deriv(g^4+4*g^3-16*g+12, g) - 4*(g-1)*(g+2)^2);
print("P(b) expansion (lem:size) = ", (27*b^3-132)^2-432*(b^2+b+1)^3 - (297*b^6-1296*b^5-2592*b^4-10152*b^3-2592*b^2-1296*b+16992));

print();
print("################ C1'/tower: 3-rank of Cl(F_b) under (towerhyp) ################");
for(i=1,8, my(b=[9,-9,63,-63,117,-117,171,225][i], cb=b*(b^3-4), K=bnfinit(polcompositum(x^2+3, x^2-cb)[1],1)); print(" b=",b," Cl(F_b)=",K.cyc," 3-rank=",sum(j=1,#K.cyc,if(K.cyc[j]%3==0,1,0))));
print("EXPECT: b=9 has 3-rank 1 (tower terminates); all other listed b have 3-rank >=2.");
