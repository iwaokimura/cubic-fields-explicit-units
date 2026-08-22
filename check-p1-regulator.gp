\\ check-p1-regulator.gp --- P1 (paper.tex revision) sanity gate.
\\ Verifies the one numerical statement rewritten during the notation pass:
\\ at a square-exception b, the regulator R = log(eta_0) satisfies
\\   R <= (1/2) log(eta_b)  and  (1/2) log(eta_b) ~ log(sqrt(3)|b|),
\\ and re-confirms the exponents n(b) with eta_b = eta_0^{n(b)} quoted in
\\ rem:star (b = -75, -3, 9) and the parity claim of thm:closed.
default(realprecision, 60);

etaorder(b) = { my(f = x^3 - 3*b*x - b^3, K, eta); K = bnfinit(f, 1); eta = 1/((b+1) - Mod(x, f)); return([abs(lift(bnfisunit(K, eta)[1])), K.reg]); };

run() = { my(bs, n, R, etab, half, ok); bs = [5, 9, 96, 112, -3, -16, -75, -135]; ok = 1; print("b   n(b)  R=log(eta_0)   (1/2)log(eta_b)   log(sqrt3*|b|)   R <= (1/2)log(eta_b)"); for(i = 1, #bs, my(b = bs[i], t = etaorder(b)); n = t[1]; R = t[2]; etab = polrootsreal(x^3 - 3*(b^2+b+1)*x^2 + 3*(b+1)*x - 1)[1]; half = log(etab)/2; if(!(R <= half + 1e-30), ok = 0); if(n % 2 != 0, ok = 0); printf("%d  %d  %.6f  %.6f  %.6f  %d\n", b, n, R, half, log(sqrt(3)*abs(b)), R <= half + 1e-30)); print(); print("EXPECT n(-75)=4, n(-3)=8, n(9)=6 (rem:star); all n even (thm:closed)"); print(if(ok, "GREEN: all n even and R <= (1/2)log(eta_b)", "RED")); return(ok); };

run();
