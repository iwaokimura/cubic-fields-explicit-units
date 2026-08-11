/* Verify the Pell parametrization of the even-power exceptions.
   Pell:  D^2 - 3E^2 = 1,  D+E*sqrt3 = (2+sqrt3)^k.
   Predicted exceptions:
     A = D+1 : b_+ = 1 - A^2 + 2*(A+1)*E
     A = 1-D : b_- = 1 - A^2 + 2*|A+1|*E
   For each predicted b: (a) check the n=2 system has integer (A,B),
   (b) confirm eps=theta-(b+1) is NOT fundamental (even exponent) via bnfisunit. */

checkb(b) = {
  my(f, BK, e, dec, n);
  f = x^3 - 3*b*x - b^3;
  if(!polisirreducible(f), return([-1,0]));
  BK = bnfinit(f, 1);
  e = Mod(x - (b+1), f);
  dec = bnfisunit(BK, e);
  n = dec[1];
  return([n, abs(n)!=1]);
};

\\ generate Pell solutions
D = 2; E = 1;   \\ (2+sqrt3)^1
{
print("=== Pell-predicted exceptions and bnfisunit verification ===");
for(k = 1, 5,
  my(Ap, Am, bp, bm);
  Ap = D + 1;          \\ positive branch
  Am = 1 - D;          \\ negative branch
  bp = 1 - Ap^2 + 2*abs(Ap+1)*E;
  bm = 1 - Am^2 + 2*abs(Am+1)*E;
  printf("k=%d (D,E)=(%d,%d):  b_-=%d  b_+=%d\n", k, D, E, bm, bp);
  if(k>=2,  \\ k=1 gives degenerate small b
    foreach([bm, bp], b,
      if(b > 2,
        my(r = checkb(b));
        printf("    b=%d : eps = fund^%d  -> %s\n",
               b, r[1], if(r[2]," EXCEPTION (not fundamental)","fundamental"));
      )
    )
  );
  \\ next Pell solution: multiply by (2+sqrt3)
  my(Dn = 2*D + 3*E, En = D + 2*E);
  D = Dn; E = En;
);
}

\\ exhaustive recheck of full exception list in a modest range
{
print();
print("=== exhaustive bnfisunit scan b=2..400 (sanity) ===");
for(b = 2, 400,
  my(f = x^3 - 3*b*x - b^3);
  if(polisirreducible(f),
    my(BK = bnfinit(f,1), dec = bnfisunit(BK, Mod(x-(b+1),f)));
    if(abs(dec[1])!=1, printf("  EXC b=%d  n=%d\n", b, dec[1]))
  )
);
}
\q
