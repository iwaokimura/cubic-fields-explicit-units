/* E012 (c) -- do the negative-b square-exceptions come from the SAME Pell
   equation D^2-3E^2=1 ?   General parametrization (E003 algebra, sign-free):
       b = 1 - A^2 + s*2*(A+1)*E ,   A in {D+1, 1-D},  s in {+1,-1}.
   Enumerate all 4 branches per Pell solution; list every integer b with b<-1.
   gp gotcha: keep each for(...) on ONE physical line. */

print("=== E012(c)  negative b from Pell D^2-3E^2=1 ===");
print("k : (D,E) -> the four b = 1-A^2 + s*2(A+1)E  (A=D+1 and A=1-D)");
emit(k,D,E) = my(L=List()); for(j=1,2, A=if(j==1,D+1,1-D); for(si=0,1, s=2*si-1; b=1-A^2+s*2*(A+1)*E; listput(L,b))); vecsort(Vec(L));
showrow(k,D,E) = bs=emit(k,D,E); printf("k=%d (D=%d,E=%d): all b = %s ;  b<-1 : %s\n", k, D, E, bs, select(x->(x<-1), bs));

D=2; E=1; for(k=1,8, showrow(k,D,E); Dn=2*D+3*E; En=D+2*E; D=Dn; E=En);

print("\n--- collect ALL b<-1 with |b|<=5000 from Pell, sorted ---");
allneg = List(); D=2; E=1; for(k=1,12, bs=emit(k,D,E); for(i=1,#bs, if(bs[i]<-1 && bs[i]>=-5000, listput(allneg,bs[i]))); Dn=2*D+3*E; En=D+2*E; D=Dn; E=En);
print("Pell-predicted negative exceptions in [-5000,-2]: ", vecsort(Vec(allneg),,8));
print("(compare with bnfisunit scan: -16, -135, -1344, -1568 were the n=2 [square] ones;");
print(" -3 (n=8) and -75 (n=4) are the non-pure-square / sporadic ones)");
