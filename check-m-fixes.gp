\\ check-m-fixes.gp --- verification of the statements newly written into paper.tex (E018 fixes M1-M11)
default(realprecision, 60);

print("### M1/M2: b != 0,1  <=>  disc<0 & irreducible; the two excluded values ###");
for(b=-4, 4, my(f=x^3-3*b*x-b^3); print(" b=",b," disc=",poldisc(f)," irred=",polisirreducible(f)," #real roots=",if(polisirreducible(f),polsturm(f),-1)));
print(" prop:setup(iii) b<theta<b+1 over |b|<=300, both signs:");
bad=0; for(b=-300,300, if(b!=0 && b!=1, my(r=polrootsreal(x^3-3*b*x-b^3)[1]); if(!(r>b && r<b+1), bad++; print("  FAIL b=",b))));
print("   failures: ",bad,"   (=> theta not in Z => f_b irreducible)");

print();
print("### M3: lem:etasize  1 < eta_b < P+1  (and eta_b > P for b<=-1) ###");
bad=0; for(b=-300,300, if(b!=0 && b!=1, my(P=3*(b^2+b+1), e=polrootsreal(x^3-P*x^2+3*(b+1)*x-1)[1]); if(!(e>1 && e<P+1), bad++; print("  FAIL b=",b)); if(b<=-1 && !(e>P), bad++; print("  FAIL(eta>P) b=",b)); if(b>=2 && !(e<P), bad++; print("  FAIL(eta<P) b=",b))));
print(" failures: ",bad);
print(" eta_{-2}  = ", polrootsreal(x^3-3*(4-2+1)*x^2+3*(-1)*x-1)[1], "  vs P=9");
print(" eta_{-100}= ", polrootsreal(x^3-3*(10000-100+1)*x^2+3*(-99)*x-1)[1], "  vs P=29703");

print();
print("### M3: lem:size (i) and (ii), new polynomials and hand-checkable bounds ###");
print(" P(b) identity: ", (27*b^3-132)^2-16*(3*b^2+3*b+4)^3 - (297*b^6-1296*b^5-3024*b^4-11016*b^3-4032*b^2-2304*b+16400));
print(" Q(c) identity: ", (27*c^3+84)^2-16*(3*c^2-3*c+4)^3 - (297*c^6+1296*c^5-3024*c^4+8424*c^3-4032*c^2+2304*c+6032));
print(" real roots of P: ", polrootsreal((27*b^3-132)^2-16*(3*b^2+3*b+4)^3), "  (both < 7)");
print(" real roots of Q: ", polrootsreal((27*c^3+84)^2-16*(3*c^2-3*c+4)^3), "  (both < 0)");
print(" 297-1296/7-3024/49-11016/343-4032/2401-2304/16807 == 272439/16807 ? ", 297-1296/7-3024/49-11016/343-4032/2401-2304/16807 == 272439/16807);
print(" (i) at b=7..12: ", vector(6,i,my(bb=i+6); 27*(bb^3-4) > 4*(3*bb^2+3*bb+4)^1.5+24));
print(" (ii) at c=2..9: ", vector(8,i,my(cc=i+1); 27*(cc^3+4) > 4*(3*cc^2-3*cc+4)^1.5+24));

print();
print("### M12: thm:mainneg extended to b <= -1: the case b=-1 (c=1) ###");
{
my(bb=-1, cc=1, f, a, dk, PP, et, K);
f = x^3-3*bb*x-bb^3; dk = nfdisc(f); a = sqrtint(abs(poldisc(f))\abs(dk));
print(" f_{-1} = ",f,"   disc = ",poldisc(f),"   a = ",a,"   D_K = ",dk);
print(" hypotheses: 3 nmid b = ",bb%3!=0,"   b^3-4 = ",bb^3-4," squarefree = ",issquarefree(bb^3-4));
print(" eq:dkbound: a^2 | |b|^3 = ",abs(bb)^3 % a^2 == 0,"   |D_K| >= 27|b^3-4| = ",27*abs(bb^3-4),"  actual ",abs(dk));
PP = 3*(bb^2+bb+1); et = polrootsreal(x^3-PP*x^2+3*(bb+1)*x-1)[1];
print(" P = ",PP,"   eta_{-1} = ",et,"   1<eta<P+1 = ",(et>1)&&(et<PP+1),"   eta>P = ",et>PP);
print(" lem:size(ii) at c=1: 27(c^3+4) = ",27*(cc^3+4)," > 4(3c^2-3c+4)^{3/2}+24 = ",4*(3*cc^2-3*cc+4)^1.5+24,"  OK = ",27*(cc^3+4) > 4*(3*cc^2-3*cc+4)^1.5+24);
print(" Q(1) = ",297*cc^6+1296*cc^5-3024*cc^4+8424*cc^3-4032*cc^2+2304*cc+6032,"  (expect 11297 > 0)");
print(" Artin chain: u <= sqrt(eta) = ",sqrt(et),"  => 4u^3+24 = ",4*sqrt(et)^3+24,"  <  |D_K| = ",abs(dk),"  OK = ",4*sqrt(et)^3+24 < abs(dk));
K = bnfinit(f,1);
print(" eta_{-1} really fundamental? bnfisunit exponent = ",abs(lift(bnfisunit(K, 1/((bb+1)-Mod(x,f)))[1])),"   bnfcertify = ",bnfcertify(K));
}
print(" (from the E018 scan |b|<=3000: every exceptional b<=-1 has b^3-4 non-squarefree,");
print("  except b=-3 which has 3|b -- so no b<=-1 meeting the extended hypothesis is an exception)");

print();
print("### M4: b squarefree, 3 nmid b, b^3-4 squarefree => a=|b|, t=0, basis {1,theta,(theta^2-3b)/b}, D_K=-27b(b^3-4) ###");
bad=0; cnt=0;
for(b=2, 400, if(b%3!=0 && issquarefree(b) && issquarefree(b^3-4), my(f=x^3-3*b*x-b^3, nf=nfinit(f), a=abs(b)); cnt++; if(sqrtint(abs(poldisc(f))\abs(nfdisc(f)))!=a || (3*(0-b))%a!=0 || (0-b^3)%(a^2)!=0 || denominator(nfalgtobasis(nf,lift(Mod((x^2-3*b)/b,f))))!=1 || nfdisc(f)!=-27*b*(b^3-4), bad++; print("  FAIL b=",b))));
for(b=-400,-2, if(b%3!=0 && issquarefree(b) && issquarefree(b^3-4), my(f=x^3-3*b*x-b^3, nf=nfinit(f), a=abs(b)); cnt++; if(sqrtint(abs(poldisc(f))\abs(nfdisc(f)))!=a || (3*(0-b))%a!=0 || (0-b^3)%(a^2)!=0 || denominator(nfalgtobasis(nf,lift(Mod((x^2-3*b)/b,f))))!=1 || nfdisc(f)!=-27*b*(b^3-4), bad++; print("  FAIL b=",b))));
print(" tested ",cnt,"  failures: ",bad);
print("### M4: rem:reduced -- f_b reduced (no p with p^2|3b, p^3|b^3) <=> 3 nmid b and b squarefree ###");
red(b) = my(ps=if(abs(b)==1, [], factor(abs(b))~[1,])); for(i=1,#ps, my(p=ps[i]); if(valuation(3*b,p)>=2 && valuation(b^3,p)>=3, return(0))); if(valuation(3*b,3)>=2 && valuation(b^3,3)>=3, return(0)); return(1);
bad=0; for(b=-400,400, if(b!=0 && b!=1, if(red(b) != (b%3!=0 && issquarefree(b)), bad++; print("  FAIL b=",b))));
print(" mismatches: ",bad);

print();
print("### M5: thm:iff reduction -- eq:branch satisfies (I),(II) on all four branches ###");
lucD(k) = round(real(((2+sqrt(3))^k+(2-sqrt(3))^k)/2));
pelE(k) = round(real(((2+sqrt(3))^k-(2-sqrt(3))^k)/(2*sqrt(3))));
bad=0; for(k=1, 12, for(i=1,4, my(sA=[1,1,-1,-1][i], sg=[1,-1,1,-1][i], D=lucD(k), Ee=pelE(k), A, B, b); A=1+sA*D; B=2*A^2-3-3*sg*Ee*(A+1); b=1-A^2+2*sg*Ee*(A+1); if(B^2-2*A != 3*(b^2+b+1) || A^2-2*B != 3*(b+1) || 3*A*(A-2) != 9*Ee^2 || D^2-3*Ee^2 != 1, bad++; print("  FAIL k=",k," i=",i))));
print(" failures over k<=12, 4 branches: ",bad);
print(" quartic/discriminant identities: ", 3*(B^2-2*A)-((A^2-2*B)^2-3*(A^2-2*B)+9) + (A^4-4*A^2*B+B^2-3*A^2+6*A+6*B+9), "  ", (4*A^2-6)^2-4*(A^4-3*A^2+6*A+9)-12*A*(A+1)^2*(A-2));
print(" consistency with thm:closed's b_pm = (2ED-3E^2-1) +- (4E-2D):");
for(k=2, 5, my(D=lucD(k), Ee=pelE(k)); print("  k=",k,"  eq:branch(A=D+1,sg=+1)=",1-(1+D)^2+2*Ee*(2+D),"  b_+=",2*Ee*D-3*Ee^2-1+(4*Ee-2*D),"   eq:branch(A=1-D,sg=-1)=",1-(1-D)^2-2*Ee*(2-D),"  b_-=",2*Ee*D-3*Ee^2-1-(4*Ee-2*D)));

print();
print("### M6: ramification of 3 and 2 as now stated in the introduction ###");
dec(b,p) = my(nf=nfinit(x^3-3*b*x-b^3), pd=idealprimedec(nf,p)); return([vector(#pd,i,[pd[i].e,pd[i].f]), valuation(nf.disc,p)]);
bad=0;
for(b=-200,200, if(b!=0 && b!=1, my(r=dec(b,3), v=r[2], tot=(#r[1]==1 && r[1][1][1]==3)); if(b%3!=0, if(!(tot && v==if(b%3==1,4,3)), bad++; print("  FAIL(3) b=",b," ",r)), my(w=valuation(b,3)); if(w%2==0, if(!(#r[1]==2 && v==1), bad++; print("  FAIL(3,even) b=",b," ",r)), if(v!=0, bad++; print("  FAIL(3,odd) b=",b," ",r))))));
print(" p=3 mismatches (|b|<=200): ",bad);
bad=0;
for(b=-200,200, if(b!=0 && b!=1, my(r=dec(b,2), v=r[2], w=valuation(b,2), bp=if(b%2==0,b/2^w,b), unram=(b%2!=0) || (w%2==0 && bp%4==3)); if(unram, if(v!=0, bad++; print("  FAIL(2,unram) b=",b," ",r)), if(!(#r[1]==2 && v==if(w%2==1,3,2)), bad++; print("  FAIL(2,ram) b=",b," ",r)))));
print(" p=2 mismatches (|b|<=200): ",bad);

print();
print("### M8: 3 nmid b => b^3 = +-1 mod 9 (so b^3 != 4 mod 9); b odd => b^3 != 4 mod 4 ###");
print(" b^3 mod 9 for 3 nmid b: ", Set(vector(200,i,my(bb=i); if(bb%3!=0, bb^3%9, 1))));
print(" b^3 mod 4 for b odd:    ", Set(vector(200,i,my(bb=2*i-1); bb^3%4)));
