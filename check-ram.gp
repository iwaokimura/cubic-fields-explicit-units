/* E015 -- make the 2,3-adic index [T]. Verify the v_p(D_K) formulas that the
   route-B proofs establish:
     p=3 (TAME, e<=2):  3∤b -> 0 ;  3|b, w=v3(b) -> (w even ? 1 : 0)
     p=2 (WILD e=2 iff w odd):  b odd -> 0 ;  2|b, w=v2(b), b'=b/2^w :
          w odd -> 3 ;  w even -> (b'≡1 mod4 ? 2 : 0)
   and that these reproduce the index exponents. Big range, both signs.
   Proof ingredients also checked: q-factor q=x^2+theta1*x+c, disc q valuations.
   gp gotchas: each for(...) on ONE line; each name(args)=... def on ONE line. */

\\ INDEX exponents (the claim to prove); and v_p(D_K) only where p ramifies via the index.
v3a_pred(b)=if(b%3!=0, 0, my(w=valuation(b,3)); (3*(w+1))\2);
v2a_pred(b)=if(b%2!=0, 0, my(w=valuation(b,2),bp=(b/2^w)); if(w%2==1, (3*w-1)/2, 3*w/2 + if(((bp%4)+4)%4==3,1,0)));
\\ v_p(D_K) the route-B proofs compute, restricted to p|b:
v3DK_pred(b)=my(w=valuation(b,3)); if(w%2==0, 1, 0);          \\ valid for 3|b
v2DK_pred(b)=my(w=valuation(b,2),bp=(b/2^w)); if(w%2==1, 3, if(((bp%4)+4)%4==1, 2, 0)); \\ valid for 2|b
ia(b)=my(f=x^3-3*b*x-b^3); sqrtint(abs(poldisc(f))\abs(nfdisc(f)));

print("=== (A) INDEX exponents v_2(a),v_3(a) vs closed form, |b|<=600 both signs ===");
bad2=0; bad3=0; n=0; chk(b)=my(a=ia(b)); n++; if(valuation(a,2)!=v2a_pred(b), bad2++; if(bad2<=6,printf("  v2(a) FAIL b=%d: %d vs %d\n",b,valuation(a,2),v2a_pred(b)))); if(valuation(a,3)!=v3a_pred(b), bad3++; if(bad3<=6,printf("  v3(a) FAIL b=%d: %d vs %d\n",b,valuation(a,3),v3a_pred(b))));
for(b=2,600, chk(b)); for(c=2,600, chk(-c));
printf("  tested %d ; v2(a) failures=%d ; v3(a) failures=%d\n", n, bad2, bad3);

print("\n=== (A') v_p(D_K) on ramified cases (3|b ; 2|b) vs route-B formula ===");
e2=0;e3=0;m2=0;m3=0; chkr(b)=my(dk=nfdisc(x^3-3*b*x-b^3)); if(b%3==0, m3++; if(valuation(dk,3)!=v3DK_pred(b), e3++)); if(b%2==0, m2++; if(valuation(dk,2)!=v2DK_pred(b), e2++));
for(b=2,600, chkr(b)); for(c=2,600, chkr(-c));
printf("  3|b: tested=%d v3(D_K) failures=%d ; 2|b: tested=%d v2(D_K) failures=%d\n", m3, e3, m2, e2);

print("\n=== (B) full index a(b) from v_p(D_K): a^2 = D_F/D_K, vs nfdisc ===");
bad=0; chk2(b)=my(f=x^3-3*b*x-b^3,DF=poldisc(f),DK=nfdisc(f),a=sqrtint(abs(DF)\abs(DK))); if(a^2*abs(DK)!=abs(DF), bad++);
for(b=2,600, chk2(b)); for(c=2,600, chk2(-c));
printf("  a^2*|D_K|=|D_F| consistency failures = %d\n", bad);

print("\n=== (C) proof certificate: q-factor disc valuations (factorpadic) ===");
print("  p=2: f = (linear over Q2)*(quadratic q); v2(disc q) and field-disc class");
q2(b)=my(w=valuation(b,2),fa=factorpadic(x^3-3*b*x-b^3,2,40)); my(deg2=0,vd=-1); for(j=1,#fa~, if(poldegree(fa[j,1])==2, deg2=1; vd=valuation(poldisc(fa[j,1]),2))); printf("  b=%4d w=%d : v2(disc q)=%d  (w odd->odd val->v2DK=3; w even->even val)\n", b, w, vd);
q2(2); q2(6); q2(10); q2(4); q2(12); q2(8); q2(16); q2(20); q2(24);
print("  p=3: 3|b, the length-2 edge -> quadratic factor over Q3");
q3(b)=my(w=valuation(b,3),fa=factorpadic(x^3-3*b*x-b^3,3,40)); my(vd=-1,dg=0); for(j=1,#fa~, if(poldegree(fa[j,1])==2, dg=2; vd=valuation(poldisc(fa[j,1]),3))); printf("  b=%4d w=%d : quad-factor present=%d v3(disc q)=%d\n", b, w, dg, vd);
q3(3); q3(9); q3(27); q3(6); q3(18); q3(15); q3(45);
quit
