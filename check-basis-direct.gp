\\ check-basis-direct.gp --- E019/P0: the integral basis without Voronoi's theorem
\\
\\ Claim (A) of PLAN-E019 section 2.1:
\\   omega := (theta^2-3b)/b  has minimal polynomial  X^3+3X^2-b^3  EXACTLY,
\\   for every b (no squarefreeness, no condition at 3).  Hence omega is an
\\   algebraic integer unconditionally, the lattice L=Z+Z.theta+Z.omega has
\\   discriminant disc(f_b)/b^2 = -27b(b^3-4) (the change of basis from
\\   (1,theta,theta^2) has determinant 1/b), and in the squarefree regime
\\   (3 nmid b, b squarefree, b^3-4 squarefree) one has a=|b| hence
\\   D_K = disc(f_b)/a^2 = -27b(b^3-4) = disc(L), so L = O_K is MAXIMAL and
\\   {1,theta,omega} is an integral basis.  This replaces the appeal to
\\   Voronoi's theorem (whose 3-adic hypotheses we had misquoted) in
\\   Corollary cor:idxmain.
\\
\\ NOTE (gp syntax): in a script a statement may span several lines only if it
\\ is enclosed in braces.

default(realprecision, 40);

print("### (0) symbolic identities of section 2.1 (b indeterminate) ###");
\\ e_i = elementary symmetric functions of theta_1,theta_2,theta_3: 0, -3b, b^3.
\\ x_i = theta_i^2, c = 3b, omega_i = (x_i-c)/b.
{
my(e1 = 0, e2 = -3*b, e3 = b^3, c = 3*b, E1x, E2x, E3x, num);
E1x = e1^2-2*e2; E2x = e2^2-2*e1*e3; E3x = e3^2;
print(" e1(x)-6b      = ", E1x-6*b);
print(" e2(x)-9b^2    = ", E2x-9*b^2);
print(" e3(x)-b^6     = ", E3x-b^6);
print(" Tr(omega)+3   = ", (E1x-3*c)/b + 3);
print(" e2(omega)     = ", (E2x-2*c*E1x+3*c^2)/b^2);
print(" e3(omega)-b^3 = ", (E3x-c*E2x+c^2*E1x-c^3)/b^3 - b^3);
\\ the same as a polynomial identity in Z[b][x]: b^3*(omega^3+3omega^2-b^3) is
num = (x^2-3*b)^3 + 3*b*(x^2-3*b)^2 - b^6;
print(" (x^2-3b)^3+3b(x^2-3b)^2-b^6  ==  0 mod f_b over Z[b] ? ",
      lift(Mod(num, x^3-3*b*x-b^3)) == 0);
print(" quotient (x^2-3b)^3+3b(x^2-3b)^2-b^6 / f_b = ",
      num \ (x^3-3*b*x-b^3));
}

print();
print("### (0') the shift X=Z-1 turns X^3+3X^2-b^3 into Ishida's shape ###");
print(" (z-1)^3+3(z-1)^2-b^3 = ", subst(x^3+3*x^2-b^3, x, z-1));
print(" so zeta = omega+1 = (theta^2-2b)/b satisfies z^3-3z-(b^3-2) = 0:");
{
print("  identity in Z[b][x]: ",
      lift(Mod((x^2-2*b)^3-3*b^2*(x^2-2*b)-b^3*(b^3-2), x^3-3*b*x-b^3)) == 0);
}
{
my(bad = 0);
for(b = -60, 60, if(b != 0 && b != 1,
  my(f = x^3-3*b*x-b^3, K1 = nfinit(f), K2 = nfinit(x^3-3*x-(b^3-2)));
  if(!polisirreducible(x^3-3*x-(b^3-2)) || nfisisom(K1, K2) == 0,
     bad++; print("  isom FAIL b=", b))));
print(" K_b = Q(root of z^3-3z-(b^3-2)) for all |b|<=60, b!=0,1: failures = ", bad);
}

print();
print("### (i)-(iii) numerical check, |b|<=400, both signs ###");
{
my(bad = 0, sfcnt = 0, nmaxout = 0);
for(b = -400, 400, if(b != 0 && b != 1,
  my(f = x^3-3*b*x-b^3, th = Mod(x,f), om, dl, sf, dk, nf, u);
  om = (th^2-3*b)/b;
  \\ (i) omega is a root of X^3+3X^2-b^3, which is thus its minimal polynomial
  if(subst(x^3+3*x^2-b^3, x, om) != Mod(0,f), bad++; print("  minpoly FAIL b=",b));
  if(minpoly(om) != x^3+3*x^2-b^3, bad++; print("  minpoly(om) FAIL b=",b));
  nf = nfinit(f);
  if(denominator(nfalgtobasis(nf, lift(om))) != 1, bad++; print("  omega not integral, b=",b));
  \\ (ii) discriminant of the lattice (1,theta,omega): determinant of the trace form
  u = [Mod(1,f), th, om];
  dl = matdet(matrix(3,3, i,j, trace(u[i]*u[j])));
  if(dl != -27*b*(b^3-4) || dl != poldisc(f)/b^2,
     bad++; print("  latticedisc FAIL b=",b," got ",dl));
  \\ (iii) in the squarefree regime the lattice is maximal and a=|b|
  dk = nf.disc; sf = (b%3 != 0 && issquarefree(b) && issquarefree(b^3-4));
  if(sf,
    sfcnt++;
    if(dl != dk, bad++; print("  MAXIMAL FAIL b=",b," disc(L)=",dl," D_K=",dk));
    if(sqrtint(abs(poldisc(f) \ dk)) != abs(b), bad++; print("  a=|b| FAIL b=",b))
  ,
    if(dl == dk, nmaxout++))
));
print(" failures = ", bad, "   squarefree-regime cases = ", sfcnt,
      "   (maximal outside the regime too: ", nmaxout, " cases)");
}

print();
print("### (iv) rem:reduced: b=25 admits no Voronoi t, yet omega is integral ###");
{
my(b = 25, f = x^3-3*b*x-b^3, nf = nfinit(f), a, ts);
a = sqrtint(abs(poldisc(f)) \ abs(nf.disc));
print(" b=25: a = ", a, "   nfbasis = ", nfbasis(f));
print(" theta/5 integral? ", denominator(nfalgtobasis(nf, lift(Mod(x/5,f)))) == 1);
ts = select(t -> (3*t^2-3*b)%a == 0 && (t^3-3*b*t-b^3)%(a^2) == 0, vector(a^2, i, i-1));
print(" #{t mod a^2 : f'(t)=0 (a), f(t)=0 (a^2)} = ", #ts, "   (0 = no Voronoi t)");
print(" omega integral at b=25? ", denominator(nfalgtobasis(nf, lift(Mod((x^2-3*b)/b,f)))) == 1);
print(" disc(L) = ", -27*b*(b^3-4), "   D_K = ", nf.disc,
      "   [O_K:L] = ", sqrtint((-27*b*(b^3-4)) \ nf.disc));
}
