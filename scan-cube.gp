\\ Tier-2 scan: for which integer b is eta = -1/eps_b a CUBE of a unit?
\\ eta = eta_0^n (n = fundamental-unit exponent from bnfisunit); eta is a cube <=> 3 | n.
\\ Conjecture (from Thue reduction): eta cube  <=>  b = 9  (all b != 0).
default(parisize, "2G");

fb(b) = x^3 - 3*b*x - b^3;
eta_of(b) = lift( Mod((b+1)-x, fb(b))^(-1) );
\\ n = signed exponent of eta w.r.t. the fundamental unit
ord_of(b) = my(f=fb(b), bnf=bnfinit(f), u=bnfisunit(bnf, Mod(eta_of(b),f))); u[1];

print("========= (A) full scan: all b in [-600,600], b!=0,±1,2, flag 3|n =========");
{ my(cubes=[]); \
  for(b=-600,600, if(b!=0 && b!=1 && b!=-1 && b!=2 && polisirreducible(fb(b)), \
    my(n=ord_of(b)); if(n%3==0, cubes=concat(cubes,[[b,n]])))); \
  print("  b with eta a cube (3|n): ", cubes); }

print("");
print("========= (B) subfamily v_3(b) even >=2, both signs, |b|<=600: list n =========");
{ for(b=-600,600, if(abs(b)>=2 && valuation(b,3)>=2 && valuation(b,3)%2==0 && polisirreducible(fb(b)), \
    my(n=ord_of(b), w3=valuation(b,3), sf=issquarefree(b^3-4)); \
    print("  b=", b, "  v3=", w3, "  b^3-4 sqfree? ", sf, "  n=", n, "  cube? ", n%3==0))); }

print("");
print("========= (C) cross-check: b=9 detail =========");
{ my(f=fb(9), bnf=bnfinit(f), eta=eta_of(9), u=bnfisunit(bnf,Mod(eta,f)), fu=bnf.fu[1]); \
  print("  b=9: eta=", eta, "  bnfisunit=", u, "  |D_K|=", bnf.disc, "  index a=", sqrtint((-poldisc(f))\(-bnf.disc))); \
  print("  fundamental unit eta_0 = ", lift(fu), "  ; candidate cube root u=eta_0^2 minpoly = ", minpoly(fu^2)); \
  print("  check u^3 == eta ? ", (fu^(u[1])==Mod(eta,f))); }
quit;
