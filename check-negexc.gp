\\ check-negexc.gp --- E019/P1: thm:exc for BOTH signs of b, unconditionally
\\
\\ New structure found in E019.  Write an exceptional b via thm:iff as
\\     A = 1+s*D,  B = 2A^2-3-3*F*(A+1),  b = 1-A^2+2*F*(A+1),
\\ where s = +-1, F = sigma*E, D^2-3E^2 = 1, E >= 0.  Put
\\     u = A+1,  w = 1-A+2F,  c = 1+F,  v = 2A^2-2A-1-3FA.
\\ Then (all identities exact over Z, using A^2-2A = 3E^2):
\\     b = u*w,      m = |AB-1| = |u*v|,      u+w = 2c,
\\     u(u-4) = 3c(c-2) = 3(E^2-1),           w(w+4-4c) = -c(c-2) = 1-E^2,
\\     v = c + (3c-5)w = 3c + u(2u-3c-3),
\\     v = 6E^2+1+2sD-3F-3sDF.
\\ MAIN LEMMA: if c != 0 then v_p(v) <= v_p(3c) for every prime p | b, i.e. the
\\ b-part g of v divides 3c; hence g <= 3|c| <= 3(E+1).
\\ SIZE: |v| > 3(E+1) for E >= 15 on all four branches, so g < |v| and v has a
\\ prime factor p not dividing b; then p | m and Lemma lem:reduc gives
\\ p^2 | b^3-4, p nmid b.  The remaining E in {0,1,4} give
\\ b in {-3,-16,9,-135,-75,5}, and b = -3 is the ONLY b where the conclusion
\\ fails (there m = m_b = 9 and b^3-4 = -31 is squarefree).

default(realprecision, 1000);
RP = 12;
lucD(k) = round(real(((2+sqrt(3))^k+(2-sqrt(3))^k)/2));
pelE(k) = round(real(((2+sqrt(3))^k-(2-sqrt(3))^k)/(2*sqrt(3))));

KMAX = 30;

print("### (0) the exact identities, k <= ", KMAX, ", all four branches ###");
{
my(bad = 0, cnt = 0);
for(k = 0, KMAX,
 for(i = 1, 4,
  my(s = [1,1,-1,-1][i], sg = [1,-1,1,-1][i], D = lucD(k), E = pelE(k), A, B, b, m, u, w, c, F);
  D = lucD(k); E = pelE(k); F = sg*E;
  A = 1+s*D; B = 2*A^2-3-3*F*(A+1); b = 1-A^2+2*F*(A+1);
  if(b != 0 && b != 1,
    cnt++;
    m = abs(A*B-1); u = A+1; w = 1-A+2*F; c = 1+F;
    if(D^2-3*E^2 != 1,               bad++; print("  Pell FAIL k=",k));
    if(A^2-2*A != 3*E^2,             bad++; print("  A^2-2A FAIL k=",k));
    if(b != u*w,                     bad++; print("  b=uw FAIL k=",k));
    if(m != abs(u*(2*A^2-2*A-1-3*F*A)), bad++; print("  m=|uv| FAIL k=",k));
    if(u+w != 2*c,                   bad++; print("  u+w=2c FAIL k=",k));
    if(u*(u-4) != 3*c*(c-2),         bad++; print("  u(u-4) FAIL k=",k));
    if(u*(u-4) != 3*(E^2-1),         bad++; print("  u(u-4)=3(E^2-1) FAIL k=",k));
    if(w*(w+4-4*c) != -c*(c-2),      bad++; print("  w(w+4-4c) FAIL k=",k));
    if(w*(w+4-4*c) != 1-E^2,         bad++; print("  w(...)=1-E^2 FAIL k=",k));
    if(2*A^2-2*A-1-3*F*A != c+(3*c-5)*w,        bad++; print("  v=c+(3c-5)w FAIL k=",k));
    if(2*A^2-2*A-1-3*F*A != 3*c+u*(2*u-3*c-3),  bad++; print("  v=3c+u(..) FAIL k=",k));
    if(2*A^2-2*A-1-3*F*A != 6*E^2+1+2*s*D-3*F-3*s*D*F, bad++; print("  v(D,E) FAIL k=",k)))));
print("  branches tested: ", cnt, "   identity failures: ", bad);
}

print();
print("### (1) MAIN LEMMA: v_p(v) <= v_p(3c) for all p | b  (c != 0) ###");
{
my(bad = 0, cnt = 0, tight = 0);
for(k = 0, KMAX,
 for(i = 1, 4,
  my(s = [1,1,-1,-1][i], sg = [1,-1,1,-1][i], D = lucD(k), E = pelE(k), A, b, u, w, c, v, F, G, g);
  D = lucD(k); E = pelE(k); F = sg*E;
  A = 1+s*D; b = 1-A^2+2*F*(A+1); u = A+1; w = 1-A+2*F; c = 1+F; v = 2*A^2-2*A-1-3*F*A;
  if(b != 0 && b != 1 && c != 0,
    cnt++;
    G = factor(abs(b));
    for(j = 1, matsize(G)[1],
      my(p = G[j,1]);
      if(valuation(v,p) > valuation(3*c,p),
         bad++; print("  FAIL k=",k," p=",p," b=",b)));
    g = prod(j = 1, matsize(G)[1], G[j,1]^valuation(v, G[j,1]));
    if((3*c) % g != 0, bad++; print("  g | 3c FAIL k=",k," b=",b));
    if(abs(g) == abs(3*c), tight++))));
print("  branches tested (c!=0): ", cnt, "   failures: ", bad,
      "   cases with g = |3c|: ", tight);
}

print();
print("### (2) SIZE: |v| > 3(E+1) for E >= 15, and the certificates ###");
{
default(realprecision, RP); print("  E^4-4E^3-2E^2+2E-1 real roots: ", polrootsreal(x^4-4*x^3-2*x^2+2*x-1), "  (all < 5)");
print("  3E^4-12E^3-18E^2-10E-3 real roots: ", polrootsreal(3*x^4-12*x^3-18*x^2-10*x-3), "  (all < 6)"); default(realprecision, 1000);
print("  (6E^2-3E+1)^2-(3E^2+1)(3E-2)^2 == 3(3E^4+2E-1) ? ",
      (6*x^2-3*x+1)^2 - (3*x^2+1)*(3*x-2)^2 == 3*(3*x^4+2*x-1));
print("  (6E^2+3E+1)^2-(3E^2+1)(3E+2)^2 == 3(3E^4-2E-1) ? ",
      (6*x^2+3*x+1)^2 - (3*x^2+1)*(3*x+2)^2 == 3*(3*x^4-2*x-1));
print("  3(3E^4+2E-1)-3(E+1)(12E^2-6E+2) == 9(E^4-4E^3-2E^2+2E-1) ? ",
      3*(3*x^4+2*x-1) - 3*(x+1)*(12*x^2-6*x+2) == 9*(x^4-4*x^3-2*x^2+2*x-1));
print("  3(3E^4-2E-1)-3(E+1)(12E^2+6E+2) = ",
      3*(3*x^4-2*x-1) - 3*(x+1)*(12*x^2+6*x+2), "  == 3E^4-12E^3-18E^2-10E-3 (times 3) ? ",
      3*(3*x^4-2*x-1) - 3*(x+1)*(12*x^2+6*x+2) == 3*(3*x^4-12*x^3-18*x^2-10*x-3));
}
{
my(bad = 0);
for(k = 3, KMAX,
 for(i = 1, 4,
  my(s = [1,1,-1,-1][i], sg = [1,-1,1,-1][i], D = lucD(k), E = pelE(k), A, b, v, F);
  D = lucD(k); E = pelE(k); F = sg*E;
  A = 1+s*D; b = 1-A^2+2*F*(A+1); v = 2*A^2-2*A-1-3*F*A;
  if(b != 0 && b != 1 && abs(v) <= 3*(E+1), bad++; print("  |v|<=3(E+1) at k=",k," b=",b))));
print("  |v| <= 3(E+1) violations for 3 <= k <= ", KMAX, ": ", bad);
}

print();
print("### (3) the finitely many E in {0,1,4}: b in {-3,-16,9,-135,-75,5} ###");
{
for(k = 0, 2,
 for(i = 1, 4,
  my(s = [1,1,-1,-1][i], sg = [1,-1,1,-1][i], D = lucD(k), E = pelE(k), A, b, u, w, c, v, F, g, sq);
  D = lucD(k); E = pelE(k); F = sg*E;
  A = 1+s*D; b = 1-A^2+2*F*(A+1); u = A+1; w = 1-A+2*F; c = 1+F; v = 2*A^2-2*A-1-3*F*A;
  if(b != 0 && b != 1,
    g = prod(j = 1, matsize(factor(abs(b)))[1],
             factor(abs(b))[j,1]^valuation(v, factor(abs(b))[j,1]));
    sq = select(p -> valuation(b^3-4, p) >= 2 && b % p != 0, factor(abs(b^3-4))~[1,]);
    print("  E=",E," b=",b," u=",u," w=",w," c=",c," v=",v," g=",g,
          "  |v|/g=",abs(v)/g,"  b^3-4=",factor(b^3-4),
          "  primes p|b^3-4 with p^2|b^3-4, p nmid b: ",sq))));
}

print();
print("### (4) conclusion: b=-3 is the only exceptional b with b^3-4 squarefree ###");
{
my(bad = 0, cnt = 0);
for(k = 0, 10,
 for(i = 1, 4,
  my(s = [1,1,-1,-1][i], sg = [1,-1,1,-1][i], D = lucD(k), E = pelE(k), A, b, F, sq);
  D = lucD(k); E = pelE(k); F = sg*E;
  A = 1+s*D; b = 1-A^2+2*F*(A+1);
  if(b != 0 && b != 1,
    cnt++;
    sq = select(p -> valuation(b^3-4, p) >= 2 && b % p != 0, factor(abs(b^3-4))~[1,]);
    if(#sq == 0 && b != -3, bad++; print("  UNEXPECTED squarefree-coprime b=", b)))));
print("  branches tested (k<=10): ", cnt, "   unexpected failures besides b=-3: ", bad);
}

print();
print("### (5) cross-check against the field: eta is a square and m = [Z[eta_0]:Z[theta]] ###");
{
my(bad = 0);
for(k = 0, 6,
 for(i = 1, 4,
  my(s = [1,1,-1,-1][i], sg = [1,-1,1,-1][i], D = lucD(k), E = pelE(k), A, B, b, m, F, f, p0);
  D = lucD(k); E = pelE(k); F = sg*E;
  A = 1+s*D; B = 2*A^2-3-3*F*(A+1); b = 1-A^2+2*F*(A+1); m = abs(A*B-1);
  if(b != 0 && b != 1 && abs(b) < 10^7,
    f = x^3-3*b*x-b^3; p0 = x^3-B*x^2+A*x-1;
    if(!polisirreducible(p0), bad++; print("  p0 reducible k=",k));
    if(nfisisom(nfinit(f), nfinit(p0)) == 0, bad++; print("  field FAIL k=",k," b=",b));
    if(poldisc(f) != m^2*poldisc(p0), bad++; print("  disc f = m^2 disc(eta_0) FAIL k=",k)))));
print("  failures: ", bad);
}
