\\ check-louboutin.gp --- the Remark comparing O_{K_b} with the order Z[eta_b].
\\
\\ Louboutin, Publ. Math. Besancon 2015, Thm 8 (= Banach Center Publ. 108
\\ (2016), Thm 8, verbatim; the classical source is Nagell 1930) decides whether
\\ a cubic unit eps > 1 of negative discriminant is the fundamental unit of the
\\ ORDER Z[eps].  It is, except when
\\   (1) Pi_eps(X) = X^3 - M^2 X^2 - 2M X - 1 for some M >= 1  (eps a square), or
\\   (2) Pi_eps is one of 8 sporadic polynomials, of discriminant -23, -31, -44.
\\ The paper's Remark claims that no member of our family is in either case, so
\\ that eta_b is ALWAYS the fundamental unit of Z[eta_b] = Z[theta], although by
\\ Theorem B it is not the fundamental unit of O_{K_b} for infinitely many b.
\\ This script checks each step of that Remark.
default(parisize, "1G");
default(realprecision, 60);

\\ minimal polynomial of eta_b, and the two coefficients P, Q of the paper
hpol(b) = { return(x^3 - 3*(b^2+b+1)*x^2 + 3*(b+1)*x - 1); };

\\ the 8 sporadic exceptions of Thm 8, transcribed from the 2016 reprint p. 175
sporadic() = { return([x^3-2*x^2+x-1, x^3-3*x^2+2*x-1, x^3-2*x^2-3*x-1, x^3-5*x^2+4*x-1, x^3-12*x^2-7*x-1, x^3-4*x^2+3*x-1, x^3-6*x^2-5*x-1, x^3-7*x^2+5*x-1]); };

\\ (a) the sporadic list really has |disc| in {23,31,44}, and a = coefficient of
\\ X^2 at most 12 -- both are used by the Remark
check_sporadic() = { my(L, ds, ok = 1); L = sporadic(); ds = vecsort(Set(apply(p -> abs(poldisc(p)), L))); print("(a) |disc| over the 8 sporadic exceptions: ", ds); if(ds != [23, 31, 44], ok = 0; print("    FAIL: expected {23,31,44}")); print("    max |coefficient of X^2|: ", vecmax(apply(p -> abs(polcoef(p, 2)), L))); return(ok); };

\\ (b) h_b is of type (T): irreducible, disc < 0, and h_b(1) = Q - P = -3b^2 < 0
\\ (c) h_b is not in the infinite family: that needs Q^2 = 4P, and
\\     9(b+1)^2 - 12(b^2+b+1) = -3(b-1)^2, so only b = 1, which is excluded
\\ (d) h_b is not sporadic: |disc(h_b)| = 27|b|^3|b^3-4| >= 135 > 44
check_family(B) = { my(ok = 1, mind = 0); for(b = -B, B, if(b != 0 && b != 1, my(h = hpol(b), P = 3*(b^2+b+1), Q = 3*(b+1), d = poldisc(h)); if(!polisirreducible(h), ok = 0; print("    FAIL irreducible b=", b)); if(d >= 0, ok = 0; print("    FAIL disc<0 b=", b)); if(subst(h, x, 1) != Q - P || Q - P != -3*b^2 || Q - P >= 0, ok = 0; print("    FAIL type (T) b=", b)); if(d != poldisc(x^3 - 3*b*x - b^3), ok = 0; print("    FAIL disc(h)=disc(f_b) b=", b)); if(9*(b+1)^2 - 12*(b^2+b+1) != -3*(b-1)^2, ok = 0; print("    FAIL identity b=", b)); if(Q^2 == 4*P, ok = 0; print("    FAIL in infinite family b=", b)); if(abs(d) != 27*abs(b)^3*abs(b^3-4), ok = 0; print("    FAIL |disc| formula b=", b)); if(mind == 0 || abs(d) < mind, mind = abs(d)); for(i = 1, #sporadic(), if(h == sporadic()[i], ok = 0; print("    FAIL sporadic b=", b))))); print("(b,c,d) all b with 0 < |b| <= ", B, ": type (T), not in the infinite family, not sporadic"); print("    min |disc(h_b)| over the range: ", mind, "   (must exceed 44)"); if(mind <= 44, ok = 0; print("    FAIL: min |disc| <= 44")); return(ok); };

\\ (e) the two answers really differ: at a square-exception, eta_b = eta_0^n with
\\     n > 1 in O_K, yet no proper root of eta_b lies in Z[theta] = Z[eta_b]
inZtheta(K, y) = { return(denominator(Vec(lift(nfbasistoalg(K, nfalgtobasis(K, y))))) == 1); };

check_split() = { my(bs, ok = 1); bs = [5, 9, 96, 112, -3, -16, -75, -135]; print("(e) square-exceptions: order of eta_b in O_K, and proper roots lying in Z[theta]"); for(i = 1, #bs, my(b = bs[i], f = x^3 - 3*b*x - b^3, K = bnfinit(f, 1)); my(eta = 1/((b+1) - Mod(x, f)), n, eta0, inz); n = abs(lift(bnfisunit(K, eta)[1])); eta0 = nfbasistoalg(K, K.fu[1]); inz = []; fordiv(n, e, if(e < n, if(inZtheta(K, eta0^e), inz = concat(inz, e)))); if(n <= 1, ok = 0; print("    FAIL: not an exception, b=", b)); if(#inz, ok = 0; print("    FAIL: a proper root lies in Z[theta], b=", b)); if(Vec(lift(minpoly(eta))) != Vec(hpol(b)), ok = 0; print("    FAIL: minpoly(eta_b) != h_b at b=", b)); printf("    b=%5d  eta_b = eta_0^%d in O_K   [O_K:Z[theta]]=%d   proper roots in Z[theta]: %s\n", b, n, K.index, if(#inz, Str(inz), "none"))); return(ok); };

run() = { my(ok = 1); if(!check_sporadic(), ok = 0); print(); if(!check_family(2000), ok = 0); print(); if(!check_split(), ok = 0); print(); print(if(ok, "GREEN: Louboutin Thm 8 never applies to this family, so eta_b is always the fundamental unit of Z[eta_b]; in O_K it is not, infinitely often", "RED")); return(ok); };

run();
