/* Validate the two inequalities the positive theorem rests on.
   (1) Artin/Ishida:  |D_K| < 4*eta0^3 + 24  for the fundamental unit eta0>1.
       Check against the ACTUAL fundamental unit (bnf) for many b,
       both exceptional and generic; report the tightest margin.
   (2) Size:  27(b^3-4) > 4*(3(b^2+b+1))^{3/2} + 24  for all b>=7,
       which (via eta < 3(b^2+b+1) and |D_K|>=27(b^3-4)) rules out
       eta=u^q for EVERY prime q>=2 at once. */

\\ (0) Self-contained PROOF of Artin's Lemma (Ishida 1973, Lemma 2):
\\     complex cubic field, unit e>1  =>  |D(e)| <= 4 e^3 + 24.
\\     Conjugates of e are e, e^{-1/2} exp(+-i*phi) (norm = +1), so
\\         |D(e)| = 4 s^{-2} (1-c^2) (s^2+1-2 s c)^2,  s = e^{3/2}, c = cos(phi).
\\     The claim 4 e^3 + 24 - |D(e)| >= 0 is, after x s^2, the polynomial
\\         F(s,c) = 4 s^4 + 24 s^2 - 4(1-c^2)(s^2-2sc+1)^2 >= 0  (s>=1, |c|<=1),
\\     which we prove via the exact sum-of-squares identity below.
{
print("=== (0) Proof core: SOS identity + reduction (exact algebra) ===");
my(F   = 4*s^4 + 24*s^2 - 4*(1-c^2)*(s^2 - 2*s*c + 1)^2,
   G   = 2*c*s^2 + 4*(1-c^2)*s + 2*c,
   SOS = (2*c*s^2 + 4*(1-c^2)*s + 2*c)^2 + 16*c^2*s^2 - 4,
   ps  = g^4 + 4*g^3 - 16*g + 12);
printf("  F - (G^2 + 16 c^2 s^2 - 4) = %s   (must be 0)\n", F - SOS);
printf("  psi'(g) - 4(g-1)(g+2)^2    = %s   (must be 0)\n", deriv(ps,g) - 4*(g-1)*(g+2)^2);
printf("  psi(0)=%d, psi(1)=%d  => psi decreasing on [0,1], min=1>0\n", subst(ps,g,0), subst(ps,g,1));
\\ numeric check of the discriminant reduction formula
my(maxerr=0.0);
for(j=1,40, my(e=1+9.0*j/40, phi=Pi*j/41, r=e^(-1/2),
   a=[e, r*exp(I*phi), r*exp(-I*phi)],
   disc=abs(((a[1]-a[2])*(a[1]-a[3])*(a[2]-a[3]))^2),
   sv=e^(3/2), cv=cos(phi),
   form=4*sv^(-2)*(1-cv^2)*(sv^2+1-2*sv*cv)^2);
   maxerr=max(maxerr, abs(disc-form)));
printf("  max |true disc - reduction formula| over grid = %.3e   (must be ~0)\n", maxerr);
print();
}

\\ (1) Artin inequality vs actual fundamental unit
{
print("=== (1) |D_K| < 4*eta0^3 + 24  (eta0 = actual fundamental unit) ===");
my(minmargin=10.0^40, worstb=0, nbad=0);
for(b=3,1500,
  my(f=x^3-3*b*x-b^3);
  if(polisirreducible(f),
    my(BK=bnfinit(f,1), dK=abs(BK.disc));
    my(fu=lift(BK.fu[1]), tr=polrootsreal(f)[1]);  \\ real root
    my(rho=abs(subst(fu, x, tr)));     \\ |real embedding of fund. unit|
    my(e0=if(rho<1, 1/rho, rho));      \\ the fundamental unit eta0>1
    my(bound=4*e0^3+24, margin=bound - dK);
    if(margin<=0, nbad++; print("  *** Artin FAILS at b=",b," |D_K|=",dK," eta0=",e0," bound=",bound));
    if(margin<minmargin, minmargin=margin; worstb=b);
  )
);
printf("  failures=%d ; tightest margin (bound-|D_K|)=%.4f at b=%d\n", nbad, minmargin, worstb);
}

\\ (2) the size inequality for b>=7 (b with 3 nmid b & b^3-4 squarefree start at 7)
{
print();
print("=== (2) 27(b^3-4) > 4*(3(b^2+b+1))^{3/2}+24 for b>=7 ? ===");
my(firstfail=0);
for(b=7,100000,
  my(lhs=27*(b^3-4), rhs=4*(3*(b^2+b+1))^(3/2)+24);
  if(!(lhs>rhs), firstfail=b; break)
);
if(firstfail, printf("  FAILS first at b=%d\n", firstfail),
              print("  holds for all b in [7,100000] (numeric)"));
\\ RIGOROUS proof (Lemma "Size inequality"): both sides>0 for b>=7, so squaring
\\ gives the equivalent polynomial P(b)>0 where
my(P = (27*b^3-132)^2 - 432*(b^2+b+1)^3);
printf("  P(b) = %s\n", P);
my(coef = 297 - 1296/7 - 2592/49 - 10152/343 - 2592/7^4 - 1296/7^5);
printf("  for b>=7, b^k<=b^6/7^(6-k) => P(b) >= (%s) b^6 + 16992 = %s b^6 + 16992 > 0  [T]\n",
       coef, coef*1.0);
printf("  real roots of P (both must be < 7): %s\n", polrootsreal(P));
\\ show margins at the low end
foreach([7,8,10,13,20], b,
  printf("    b=%d: lhs=%d rhs=%.1f margin=%.1f\n", b, 27*(b^3-4), 4*(3*(b^2+b+1))^(3/2)+24*1.0, 27*(b^3-4)-(4*(3*(b^2+b+1))^(3/2)+24)));
}
\q
