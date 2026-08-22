\\ check-p4-identities.gp --- P4 (paper.tex revision) sanity gate.
\\ P4 replaced several routine expansions by one-line statements.  This script
\\ checks, over the Pell parametrisation itself (exact integer arithmetic), every
\\ identity whose verification was compressed:
\\   thm:iff   : (I),(II) and eq:quartic;
\\   lem:uzw   : b = uw, m = |AB-1| = |uz|, u+w = 2c, eq:uzw2, eq:uzw3, and the
\\               common value 6E^2-1+A(2-3E) of the two expressions for z;
\\   lem:zsize : z = z_1 + z_2 with z_1 = 6E^2-3E+1, z_2 = sD(2-3E).
default(realprecision, 38);

pell(n) = { my(v); v = [2, 3; 1, 2]^abs(n); if(n >= 0, return([v[1,1], v[2,1]]), return([v[1,1], -v[2,1]])); };

one(n, sg) = { my(D, E, A, B, b, u, w, c, z, ok); D = pell(n)[1]; E = pell(n)[2]; A = 1 + sg*D; B = 2*A^2 - 3 - 3*E*(A+1); b = 1 - A^2 + 2*E*(A+1); u = A + 1; w = 1 - A + 2*E; c = 1 + E; z = 2*A^2 - 2*A - 1 - 3*E*A; ok = 1; if(B^2 - 2*A != 3*(b^2+b+1), ok = 0; print("FAIL (I)  n=", n)); if(A^2 - 2*B != 3*(b+1), ok = 0; print("FAIL (II) n=", n)); if(A^4 - 4*A^2*B + B^2 - 3*A^2 + 6*A + 6*B + 9 != 0, ok = 0; print("FAIL quartic n=", n)); if(A^2 - 2*A != 3*E^2, ok = 0; print("FAIL A^2-2A n=", n)); if(b != u*w, ok = 0; print("FAIL b=uw n=", n)); if(abs(A*B-1) != abs(u*z), ok = 0; print("FAIL m=|uz| n=", n)); if(u + w != 2*c, ok = 0; print("FAIL u+w n=", n)); if(u*(u-4) != 3*c*(c-2) || 3*c*(c-2) != 3*(E^2-1), ok = 0; print("FAIL uzw2a n=", n)); if(w*(w+4-4*c) != -c*(c-2) || -c*(c-2) != 1-E^2, ok = 0; print("FAIL uzw2b n=", n)); if(z != c + (3*c-5)*w, ok = 0; print("FAIL uzw3a n=", n)); if(z != 3*c + u*(2*u-3*c-3), ok = 0; print("FAIL uzw3b n=", n)); if(z != 6*E^2 - 1 + A*(2-3*E), ok = 0; print("FAIL z common value n=", n)); if(z != (6*E^2-3*E+1) + sg*D*(2-3*E), ok = 0; print("FAIL z=z_1+z_2 n=", n)); return([ok, b, z]); };

run() = { my(ok = 1, t, bs = []); for(n = -8, 8, forstep(sg = 1, -1, -2, t = one(n, sg); if(!t[1], ok = 0); if(t[2] != 0 && t[2] != 1, bs = concat(bs, t[2])))); print("b values produced (n = -8..8, both signs), excluding the degenerate 0 and 1:"); print("  ", vecsort(bs)); print(); print("checked 34 parameter pairs (A,E)"); print(if(ok, "GREEN: every identity of thm:iff, lem:uzw and lem:zsize holds exactly", "RED")); return(ok); };

run();
