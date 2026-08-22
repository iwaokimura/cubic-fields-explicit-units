\\ check-p2-nofixsq.gp --- P2 (paper.tex revision) sanity gate for lem:nofixsq.
\\ The lemma merges the two congruence checks that Theorem thm:inf (Erdos) and
\\ Corollary cor:primeb (Helfgott) used to make separately:
\\   for f(x) = x^3-4 and f(x) = x^3+4 and every prime q, some unit x mod q^2
\\   has f(x) != 0 mod q^2.
\\ Proved in the paper for all q; here it is checked for all q < 200, together
\\ with the count "at most three solutions" used for q >= 5.
default(realprecision, 38);

solcount(q, sgn) = { my(m = q^2, c = 0); for(x = 0, m-1, if(gcd(x, q) == 1 && Mod(x, m)^3 == Mod(sgn*4, m), c++)); return(c); };

run() = { my(ok = 1, nm, np); forprime(q = 2, 200, nm = solcount(q, 1); np = solcount(q, -1); if(nm >= eulerphi(q^2) || np >= eulerphi(q^2), ok = 0; print("FAIL q=", q)); if(q >= 5 && (nm > 3 || np > 3), ok = 0; print("FAIL >3 solutions at q=", q)); if(q <= 13, print("q=", q, "  #units with x^3=4: ", nm, "   #units with x^3=-4: ", np, "   phi(q^2)=", eulerphi(q^2)))); print(); print(if(ok, "GREEN: for every prime q < 200 both x^3-4 and x^3+4 miss 0 mod q^2 at some unit x, and have at most 3 unit solutions for q >= 5", "RED")); return(ok); };

run();
