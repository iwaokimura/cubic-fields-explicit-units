\\ Tier-3: eta is a cube of a unit  <=>  b in a finite Thue-determined set.
\\ Verify the algebraic reduction as polynomial identities, then solve the Thue eq.
default(parisize, "2G");

print("===== (0a) Newton: cube of a root of X^3-BX^2+AX-1 has char poly");
print("           Y^3-(B^3-3AB+3)Y^2+(A^3-3AB+3)Y-1  (identity in A,B) =====");
{ my(p = x^3 - B*x^2 + A*x - 1, \
     R = polresultant(p, y - x^3, x), \
     target = y^3 - (B^3-3*A*B+3)*y^2 + (A^3-3*A*B+3)*y - 1); \
  print("   Res_x(p, y-x^3) - target = ", R - target, "   (0 = OK)"); }

print("");
print("===== (0b) our data: P=3(b^2+b+1), Q=3(b+1);  cube system E1,E2 =====");
\\ E1: A^3-3AB = Q-3 = 3b ;  E2: B^3-3AB = P-3 = 3b(b+1) ;  E3=E2-E1: B^3-A^3=3b^2
{ my(P=3*(b^2+b+1), Q=3*(b+1)); \
  print("   Q-3 - 3b        = ", Q-3 - 3*b,          "   (0=OK)"); \
  print("   P-3 - 3b(b+1)   = ", P-3 - 3*b*(b+1),    "   (0=OK)"); }

print("");
print("===== (0c) substitute A=3a, B=3g3, b=9a(a^2-g3):  E1 holds identically,");
print("           and E2 residual == 27 * E6,  E6 = g3^3-a^3-9a^2(a^2-g3)^2 =====");
\\ E1: A^3-3AB-3b ;  E2: B^3-3AB-3b(b+1) ;  cube system is E1=E2=0.
{ my(a=aa, g3=gg, A=3*a, B=3*g3, b=9*a*(a^2-g3), \
     E1res = A^3 - 3*A*B - 3*b, \
     E2res = B^3 - 3*A*B - 3*b*(b+1), \
     E6 = g3^3 - a^3 - 9*a^2*(a^2-g3)^2); \
  print("   E1 residual A^3-3AB-3b            = ", E1res, "   (0 identically: defines b)"); \
  print("   E2 residual (B^3-3AB-3b(b+1)) - 27*E6 = ", E2res - 27*E6, "   (0=OK: E2 <=> E6)"); }

print("");
print("===== (0d) gcd step a=a1*d, g3=d*g, a1^2=1  =>  E6 = d^3*(THUE - a1) =====");
{ for(s=1,2, my(a1=[1,-1][s], \
     a = a1*d, g3 = d*g, \
     E6 = g3^3 - a^3 - 9*a^2*(a^2-g3)^2, \
     THUE = g^3 - 9*d*g^2 + 18*d^2*g - 9*d^3, \
     resid = E6 - d^3*(THUE - a1)); \
   print("   a1=", a1, " :  E6 - d^3*(THUE - a1) = ", resid, "   (0=OK)")); }

print("");
print("===== (0e) b-map:  b = 9*a1*d^2*(d-g)   (from b=9a(a^2-g3), a=a1 d, g3=d g) =====");
{ for(s=1,2, my(a1=[1,-1][s], a=a1*d, g3=d*g, \
     bfull = 9*a*(a^2-g3), bmap = 9*a1*d^2*(d-g)); \
   print("   a1=", a1, " :  9a(a^2-g3) - 9*a1*d^2*(d-g) = ", bfull - bmap, "   (0=OK)")); }

print("");
print("===== (1) irreducibility of the Thue form t^3-9t^2+18t-9 =====");
print("   polisirreducible = ", polisirreducible(x^3-9*x^2+18*x-9));

print("");
print("===== (2) solve Thue  g^3-9dg^2+18d^2g-9d^3 = ±1  (unconditional, flag=1) =====");
{ my(tnf = thueinit(x^3-9*x^2+18*x-9, 1), \
     solp = thue(tnf, 1), solm = thue(tnf, -1), bs = []); \
  print("   solutions of Phi=+1 (a1=+1): ", solp); \
  print("   solutions of Phi=-1 (a1=-1): ", solm); \
  for(i=1,#solp, my(g=solp[i][1], d=solp[i][2], b=9*1*d^2*(d-g)); bs=concat(bs,[b])); \
  for(i=1,#solm, my(g=solm[i][1], d=solm[i][2], b=9*(-1)*d^2*(d-g)); bs=concat(bs,[b])); \
  bs = vecsort(bs,,8); \
  print("   => b = 9*a1*d^2*(d-g) over all solutions: ", bs); \
  print("   => nonzero cube-exceptions: ", select(x->x!=0, bs)); }

print("");
print("===== (3) sanity: for each nonzero b above, is eta actually a cube? =====");
{ my(bl=[9]); \
  for(i=1,#bl, my(b=bl[i], f=x^3-3*b*x-b^3, bnf=bnfinit(f), \
     eta=lift(Mod((b+1)-x,f)^(-1)), n=bnfisunit(bnf,Mod(eta,f))[1]); \
   print("   b=", b, "  n=", n, "  3|n (cube)? ", n%3==0)); }
quit;
