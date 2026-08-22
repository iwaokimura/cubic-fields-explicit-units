\\ check-p3-3rank.gp --- P3 (paper.tex revision): pin down the range of the
\\ numerical remark at the end of Section 6, which said only "in the range
\\ tested".  For every b with v_3(b) even and >= 2 (the hypothesis eq:towerhyp),
\\ b != 9, both signs, |b| <= NMAX, compute the 3-rank of the class group of
\\ F_b = Q(sqrt(-3), sqrt(b(b^3-4))) and check that it is >= 2.
\\ bnfcertify makes each class group unconditional (no GRH).
default(parisize, "2G");

hyp(b) = { my(w); if(b == 0 || b == 9, return(0)); w = valuation(b, 3); return(w >= 2 && w % 2 == 0); };

rank3(b) = { my(g, bnf, cyc, r); g = polcompositum(x^2 + 3, x^2 - b*(b^3 - 4))[1]; bnf = bnfinit(g, 1); if(bnfcertify(bnf) != 1, error("bnfcertify failed at b=", b)); cyc = bnf.clgp[2]; r = sum(i = 1, #cyc, if(cyc[i] % 3 == 0, 1, 0)); return([r, cyc]); };

run() = { my(NMAX = 100, ok = 1, cnt = 0, t); for(a = 1, NMAX, forstep(sgn = 1, -1, -2, my(b = sgn*a); if(hyp(b), cnt++; t = rank3(b); if(t[1] < 2, ok = 0; print("FAIL b=", b, "  Cl=", t[2])); print("b=", b, "  Cl(F_b)=", t[2], "  3-rank=", t[1])))); print(); print("tested ", cnt, " values of b with 0 < |b| <= ", NMAX, ", v_3(b) even >= 2, b != 9 (both signs), class groups certified"); print(if(ok, "GREEN: 3-rank >= 2 throughout", "RED")); return(ok); };

run();
