/* E015 route A -- cross-check the index closed form against Llorente-Nart 1983
   (Proc AMS 87, 579-585). Their poly f=X^3 - a X + b, Delta=4a^3-27b^2=i(theta)^2 D.
   Our f_b=X^3-3bX-b^3  =>  a_LN=3b, b_LN=-b^3, Delta=-27 b^3(b^3-4).
   Implement their Theorem 2 v_p(D), with the reduction (1) [theta/p when
   v_p(a)>=2 & v_p(b)>=3], for p=2 and p>3 (clean), and an attempt at p=3.
   Verify: v_p(D)_LN == v_p(nfdisc); and v_p(index)=(v_p(Delta)-v_p(D))/2 == closed form.
   gp gotchas: each for(...) on ONE line; each name(args)=... def on ONE line. */

redLN(p,ab)=my(a=ab[1],b=ab[2]); while(valuation(a,p)>=2 && valuation(b,p)>=3, a=a/p^2; b=b/p^3); [a,b];
v2D_LN(a0,b0)=my(ab=redLN(2,[a0,b0]),a=ab[1],b=ab[2],d=4*a^3-27*b^2,s=valuation(d,2),D2=truncate(d/2^s)); if(s%2==1, 3, if((1<=valuation(b,2) && valuation(b,2)<=valuation(a,2)) || (s%2==0 && ((D2%4)+4)%4==3), 2, 0));
vpD_LN(p,a0,b0)=my(ab=redLN(p,[a0,b0]),a=ab[1],b=ab[2],d=4*a^3-27*b^2,s=valuation(d,p)); if(1<=valuation(b,p) && valuation(b,p)<=valuation(a,p), 2, if(s%2==1, 1, 0));

\\ p=3 attempt (Theorem 2, p=3), reduced coords:
v3D_LN(a0,b0)=my(ab=redLN(3,[a0,b0]),a=ab[1],b=ab[2],d=4*a^3-27*b^2,s=valuation(d,3),va=valuation(a,3),vb=valuation(b,3),am9=((a%9)+9)%9,bm3=((b%3)+3)%3,b2m9=((b^2%9)+9)%9,b2m27=((b^2%27)+27)%27,ap1m9=(((a+1)%9)+9)%9,ap1m27=(((a+1)%27)+27)%27); if(1<=vb && vb<va, return(5)); if((va==2&&vb==2) || (am9==3 && bm3!=0 && b2m9!=4), return(4)); if((va==1&&vb==1) || (va>=1 && bm3!=0 && am9!=3 && b2m9!=ap1m9) || (am9==3 && b2m9==4 && b2m27!=ap1m27), return(3)); if((va==1&&va<vb) || (va>=1 && am9!=3 && b2m9==ap1m9) || (am9==3 && b2m27==ap1m27 && s%2==1), return(1)); return(0);

aLN(b)=3*b;
bLN(b)=-b^3;
idxof(b)=my(f=x^3-3*b*x-b^3); sqrtint(abs(poldisc(f))\abs(nfdisc(f)));

print("=== route A: L-N Theorem 2 v_p(D) vs nfdisc, |b|<=300 both signs ===");
e2=0; e3=0; e5=0; n=0;
chk(b)=my(f=x^3-3*b*x-b^3,dk=nfdisc(f),P=factor(abs(dk))); n++; if(v2D_LN(aLN(b),bLN(b))!=valuation(dk,2), e2++; if(e2<=6,printf("  p2 b=%d LN=%d nf=%d\n",b,v2D_LN(aLN(b),bLN(b)),valuation(dk,2)))); if(v3D_LN(aLN(b),bLN(b))!=valuation(dk,3), e3++; if(e3<=6,printf("  p3 b=%d LN=%d nf=%d\n",b,v3D_LN(aLN(b),bLN(b)),valuation(dk,3)))); for(j=1,#P~, if(P[j,1]>=5 && vpD_LN(P[j,1],aLN(b),bLN(b))!=P[j,2], e5++));
for(b=2,300, chk(b)); for(c=2,300, chk(-c));
printf("  tested %d : v2(D) fails=%d ; v3(D) fails=%d ; p>=5 fails=%d\n", n, e2, e3, e5);

print("\n=== route A: L-N => index v_p(i), compare to actual index, |b|<=300 ===");
bad=0; chk2(b)=my(f=x^3-3*b*x-b^3,DF=poldisc(f),id=idxof(b)); my(vi2=(valuation(DF,2)-v2D_LN(aLN(b),bLN(b)))/2, vi3=(valuation(DF,3)-v3D_LN(aLN(b),bLN(b)))/2); if(vi2!=valuation(id,2) || vi3!=valuation(id,3), bad++; if(bad<=8,printf("  b=%d : LN-index v2=%d v3=%d ; actual v2=%d v3=%d\n",b,vi2,vi3,valuation(id,2),valuation(id,3))));
for(b=2,300, chk2(b)); for(c=2,300, chk2(-c));
printf("  index(from L-N) vs actual at p=2,3 : failures=%d\n", bad);
quit
