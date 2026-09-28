\\ check-baker-abc.gp --- E136: Baker's explicit abc-conjecture bounds the exceptions
\\ to (star) for 3 nmid b EFFECTIVELY.
\\
\\ (star)   |D_K| >= 4*(3(b^2+b+1)+1)^(3/5) + 24          (paper.tex, eq:star)
\\
\\ Baker's explicit abc [LS12, Conj. 1.2]: a+b'=c, pairwise coprime, N = rad(ab'c),
\\ w = omega(N)  ==>  c < (6/5) N (log N)^w / w!.
\\
\\ Sections
\\  (1) Tier 1: the four triples, their radicals, c >= |b|^3/4, N <= 2 rad(b) rad(b^3-4),
\\      N <= 2 R k t a, and Baker's inequality itself (answer check, not a test of it).
\\  (2) Tier 1: (star) holds for every 3 nmid b, 3 <= |b| <= 10^4 (via |D_K| >= 27Rt,
\\      falling back to nfdisc), so the analytic part may assume |b| > 10^4.
\\  (3) Tier 2: the constants C1 = 29/100 and K = 108/100, and c1 <= 2, in exact
\\      rational arithmetic.
\\  (4) Tier 2: the threshold W0 and the exact certificate of
\\          W0*((2/13) X0(W0) - 1 - log X0(W0)) >= 2,   X0(W0) > 13/2,
\\      with X0(i) = log i + log log i - 1.076869; then L0 = W0*X0(W0) and
\\      Lambda = (5/13) L0 (upper bounds by exact rational exp-series bounds).
\\  (5) Tier 2: reproduce the table of [LS12] Thm 1 (omega_eps, N_eps) -- answer check
\\      for our reading of X0 and of (7), (8).
\\  (6) Tier 3 comparison (8b of the plan): LS12's own route with eps = 2/13.
\\
\\ The derivation is in sections/E136.tex.

if(default(parisize) < 400000000, default(parisize, 400000000));

FAIL = 0;
check(c, msg) = { if(!c, printf("   [FAIL] %s\n", msg); FAIL++); return(c); };

ROBIN = 1076869/1000000;

rad(n) = { my(F = factor(abs(n))); return(prod(j = 1, #F[,1], F[j,1])); };

\\ R = prod of p with v_p odd  (the squarefree part of |n|)
sqfpart(n) = { return(core(abs(n))); };

\\ The coprime triple [a, b', c] for the parameter b (plan (2b)).
triple(b) = {
  if(b % 2 != 0,
    if(b > 0, return([4, b^3-4, b^3]), return([4, abs(b)^3, abs(b)^3+4])));
  my(be = b/2);
  if(b > 0, return([1, 2*be^3-1, 2*be^3]));
  return([1, 2*abs(be)^3, 2*abs(be)^3+1]);
};

\\ exact: does (star) hold?  |D| >= 4 A^(3/5) + 24  <=>  (|D|-24)^5 >= 4^5 A^3
starholds(D, b) = {
  my(A = 3*(b^2+b+1)+1, d = abs(D) - 24);
  if(d < 0, return(0));
  return(d^5 >= 4^5 * A^3);
};

\\ ---------------------------------------------------------------- (1)
tier1() = {
  my(bad = 0, cnt = 0, worstmargin = -oo, wmb = 0, bestq = 0, bq = 0);
  print("### (1) the triples: coprime, N formula, c >= |b|^3/4, N <= 2 R k t a, Baker ###");
  for(b = -10000, 10000, if(b >= -1 && b <= 2, next); if(b % 3 == 0, next);
    my(T = triple(b), a = T[1], bp = T[2], c = T[3], N, R, k, t, aa, w, L, marg, q);
    cnt++;
    if(a <= 0 || bp <= 0 || a + bp != c, bad++; print("  triple FAIL b=", b));
    if(gcd(a, bp) != 1 || gcd(a, c) != 1 || gcd(bp, c) != 1, bad++; print("  coprime FAIL b=", b));
    N = rad(a*bp*c);
    if(b % 2 != 0,
      if(N != 2*rad(b)*rad(b^3-4), bad++; print("  N (odd) FAIL b=", b)),
      if(2*N != rad(b)*rad(b^3-4), bad++; print("  N (even) FAIL b=", b)));
    if(N > 2*rad(b)*rad(b^3-4), bad++; print("  N <= 2 rad rad FAIL b=", b));
    if(4*c < abs(b)^3, bad++; print("  c >= |b|^3/4 FAIL b=", b));
    R = sqfpart(b); k = sqrtint(abs(b) \ R);
    t = sqfpart(b^3-4); aa = sqrtint(abs(b^3-4) \ t);
    if(R*k^2 != abs(b) || t*aa^2 != abs(b^3-4), bad++; print("  R k^2, t a^2 FAIL b=", b));
    if(N > 2*R*k*t*aa, bad++; print("  N <= 2 R k t a FAIL b=", b));
    \\ Baker (float; this is an answer check of the script, not of the conjecture)
    w = omega(N); L = log(N);
    marg = log(c) - (log(6/5) + L + w*log(L) - lngamma(w+1));
    if(marg >= 0, bad++; print("  Baker's inequality FAILS at b=", b, "  margin ", marg));
    if(marg > worstmargin, worstmargin = marg; wmb = b);
    q = log(c)/L;
    if(q > bestq, bestq = q; bq = b));
  print("  tested ", cnt, " values (3 nmid b, |b| <= 10^4);   failures: ", bad);
  check(bad == 0, "E136(1): triples coprime, N formula, c>=|b|^3/4, N<=2Rkta, Baker holds, |b|<=10^4");
  printf("  max abc quality log c/log N = %.5f at b = %d\n", bestq, bq);
  printf("  closest to Baker's bound: log c - log RHS = %.4f at b = %d\n", worstmargin, wmb);
  \\ the tightest case of E020(b), b = -100
  my(T = triple(-100), N = rad(T[1]*T[2]*T[3]), q = log(T[3])/log(N), qE020);
  print("  b = -100: coprime triple ", T, ",  N = ", N, " = ", factor(N)[,1]~);
  printf("    quality = %.4f\n", q);
  check(T == [1, 250000, 250001] && N == 2*5*53*89, "E136(1): b=-100 triple and radical");
  \\ E020(d) wrote 1.1373 for (4, 10^6, 1000004): not coprime, and 2 counted three times
  qE020 = log(1000004.)/log(2*10*(2*53*89));
  printf("    E020's 1.1373 = log(1000004)/log(2*10*(2*53*89)) = %.4f: the triple has gcd %d\n",
         qE020, gcd(4, 10^6));
  printf("    and the true radical of 4*10^6*1000004 is %d, not %d\n",
         rad(4*10^6*1000004), 2*10*(2*53*89));
  check(abs(qE020 - 1.1373) < 1e-4 && gcd(4, 10^6) == 4, "E136(1): E020's 1.1373 reproduced as a miscount");
  return(bad);
};

\\ ---------------------------------------------------------------- (2)
tier1star() = {
  my(bad = 0, cnt = 0, nfd = 0, minr = oo, mb = 0);
  print("### (2) (star) for 3 nmid b, 3 <= |b| <= 10^4 ###");
  for(b = -10000, 10000, if(b >= -1 && b <= 2, next); if(b % 3 == 0, next);
    my(R = sqfpart(b), t = sqfpart(b^3-4), r);
    cnt++;
    \\ |D_K| >= 27 R t (E020(b), [T]); so 27Rt already satisfying (star) settles b.
    if(!starholds(27*R*t, b),
      nfd++;
      if(!starholds(nfdisc(x^3-3*b*x-b^3), b), bad++; print("  (star) FAILS at b=", b)));
    r = 1.0*R*t/abs(b)^(6/5);
    if(r < minr, minr = r; mb = b));
  print("  tested ", cnt, ";  settled by 27Rt: ", cnt - nfd, ";  needed nfdisc: ", nfd,
        ";  (star) failures: ", bad);
  printf("  min R t / |b|^(6/5) = %.4f at b = %d\n", minr, mb);
  check(bad == 0, "E136(2): (star) holds for all 3 nmid b, 3<=|b|<=10^4");
  return(bad);
};

\\ ---------------------------------------------------------------- exact exp bounds
\\ for rational q >= 0:  explo(q,n) <= e^q <= exphi(q,n)   (exphi needs q < n+2)
explo(q, n) = {
  my(s = 1, term = 1);
  for(j = 1, n, term = term*q/j; s += term);
  return(s);
};
exphi(q, n) = {
  my(term = q^(n+1)/(n+1)!);
  if(q >= n+2, error("exphi: q too large"));
  return(explo(q, n) + term/(1 - q/(n+2)));
};
NEXP = 300;
DEN = 2^200;
\\ rational r <= log(x), certified by exp(r) <= exphi(r) <= x
loglo(x) = {
  my(r = floor(log(x)*DEN)/DEN - 1/2^190);
  if(r <= 0, error("loglo: needs x > 1"));
  if(exphi(r, NEXP) > x, error("loglo: certificate failed"));
  return(r);
};
\\ rational r >= log(x), certified by exp(r) >= explo(r) >= x
loghi(x) = {
  my(r = ceil(log(x)*DEN)/DEN + 1/2^190);
  if(explo(r, NEXP) < x, error("loghi: certificate failed"));
  return(r);
};

\\ ---------------------------------------------------------------- (3)
constants() = {
  my(C1 = 29/100, A0 = 3 + 3/10^4 + 4/10^8, K = 108/100, ok1, ok2, ok3);
  print("### (3) constants for |b| > 10^4 ###");
  \\ phi(x) = 4(3+3/x+4/x^2)^(3/5) + 24 x^(-6/5) decreases in x; at x = 10^4,
  \\ x^(-6/5) <= x^(-1), so phi(10^4) <= 27 C1 follows from A0^3 <= ((27C1 - 24/10^4)/4)^5.
  ok1 = (A0^3 <= ((27*C1 - 24/10^4)/4)^5);
  printf("  27*C1 = %.4f;  phi(10^4) <= 27*C1: %d\n", 27*C1, ok1);
  \\ K^2 >= 4 C1 (1 + 4/|b|^3) for |b| > 10^4
  ok2 = (4*C1*(1 + 4/10^12) <= K^2);
  printf("  K = %.2f;  4 C1 (1+4*10^-12) = %.6f <= K^2 = %.4f: %d\n", K, 4*C1*(1+4/10^12), K^2, ok2);
  \\ c1 = log(24/5) + (15/13) log K <= 2  <=  (24/5) K^2 <= explo(2,4) <= e^2  (K^(15/13) <= K^2)
  ok3 = ((24/5)*K^2 <= explo(2, 4));
  printf("  c1 = log(24/5) + (15/13) log K = %.5f <= 2: %d\n", log(24/5) + (15/13)*log(K), ok3);
  check(ok1 && ok2 && ok3, "E136(3): C1 = 29/100 for |b|>10^4, K = 108/100, c1 <= 2 (exact)");
  return(ok1 && ok2 && ok3);
};

\\ ---------------------------------------------------------------- (4)
X0(W) = { return(log(W) + log(log(W)) - ROBIN); };
F4(W) = { my(X = X0(W)); return(W*((2/13)*X - 1 - log(X)) - 2); };

threshold() = {
  my(lo = 1000, hi = 10^15, W0, l1, l2, u1, u2, Xlo, Xhi, ul, lhs, L0hi, Lam, ok);
  print("### (4) the threshold W0, L0 = W0 X0(W0), and Lambda = (5/13) L0 ###");
  if(!(F4(lo) < 0 && X0(lo) > 13/2 && F4(hi) > 0), error("threshold: bad bracket"));
  while(hi - lo > 1, my(m = (lo + hi) \ 2); if(F4(m) >= 0, hi = m, lo = m));
  W0 = hi;
  printf("  W0 = %d  (= %.6e);  float F4(W0) = %.3e,  F4(W0-1) = %.3e\n",
         W0, W0, F4(W0), F4(W0-1));
  \\ exact certificate
  l1 = loglo(W0); l2 = loglo(l1);           \\ l1 <= log W0,  l2 <= log l1 <= loglog W0
  u1 = loghi(W0); u2 = loghi(u1);           \\ u1 >= log W0,  u2 >= log u1 >= loglog W0
  Xlo = l1 + l2 - ROBIN; Xhi = u1 + u2 - ROBIN;
  ul = loghi(Xlo);                           \\ ul >= log Xlo
  lhs = W0*((2/13)*Xlo - 1 - ul);            \\ <= W0*((2/13)X0 - 1 - log X0), as X0 >= Xlo > 13/2
  ok = (Xlo > 13/2) && (lhs >= 2);
  printf("  certified: Xlo = %.30f\n             Xhi = %.30f\n", Xlo, Xhi);
  printf("  W0*((2/13)Xlo - 1 - log Xlo) - 2 >= %.3e   (exact rational, must be >= 0)\n", lhs - 2);
  check(ok, "E136(4): exact certificate W0((2/13)X0-1-log X0) >= 2, X0 > 13/2 at W0");
  \\ also: the smaller integer does NOT satisfy it (float; W0 is the least one)
  check(F4(W0-1) < 0, "E136(4): W0 is the least integer (float)");
  L0hi = W0*Xhi;
  Lam = (5/13)*L0hi;
  printf("  L0 = W0*X0(W0) <= %.10e\n", L0hi);
  printf("  Lambda = (5/13) L0 <= %.10e   (log|b| < Lambda; log10|b| < %.6e)\n", Lam, Lam/log(10));
  printf("  omega_max at L0: W0 = %.4e distinct primes;  X0(W0) = %.6f\n", W0, Xhi);
  return([W0, L0hi, Lam]);
};

\\ ---------------------------------------------------------------- (5)
\\ [LS12] (7): omega1 = least i >= 5 with eps X0(j) - log X0(j) >= 1 for all j >= i.
\\ eps X - log X is increasing for X > 1/eps, and X0 is increasing, so it suffices to
\\ find the least i past which it holds and check it stays (it does once X0 > 1/eps).
ls_omega1(eps) = {
  my(i = 5);
  while(!(eps*X0(i) - log(X0(i)) >= 1 && X0(i) > 1/eps), i++);
  \\ walk back while it still holds
  while(i > 5 && eps*X0(i-1) - log(X0(i-1)) >= 1, i--);
  return(i);
};
\\ [LS12] (8): least w <= omega1 such that for all w <= i <= omega1:
\\   theta(p_i) >= i/eps  and  log i! + eps theta(p_i) - i log theta(p_i) > log sqrt(2 pi i)
ls_omegaeps(eps, om1, th) = {
  my(w = om1 + 1);
  while(w > 1,
    my(i = w - 1, T = th[i]);
    if(T >= i/eps && lngamma(i+1) + eps*T - i*log(T) > log(sqrt(2*Pi*i)), w--, break));
  if(w > om1, error("ls_omegaeps: (8) fails at omega1"));
  return(w);
};
lstable() = {
  my(E = [3/4, 7/12, 6/11, 1/2, 34/71, 5/12, 1/3],
     TW = [14, 49, 72, 127, 175, 548, 6460], TWsec3 = [14, 49, 72, 127, 175, 548, 6458],
     TO1 = [15, 49, 72, 129, 176, 566, 6458],  \\ the omega1 row, commented out in arXiv v1
     TN = [37.1101, 204.75, 335.71, 679.585, 1004.763, 3894.57, 63727],
     P = primes(7000), th = vector(7000), s = 0., O1 = vector(7), OE = vector(7), ok);
  print("### (5) [LS12] Theorem 1 table: reproduced, with three discrepancies ###");
  for(i = 1, 7000, s += log(P[i]); th[i] = s);
  print("  eps       omega1  omega_eps  LS Thm1  LS sec3   theta(p_{omega_eps})   LS N_eps");
  for(j = 1, #E,
    my(e = E[j], o1 = ls_omega1(e), oe = ls_omegaeps(e, o1, th));
    O1[j] = o1; OE[j] = oe;
    printf("  %-8s  %6d  %9d  %7d  %7d   %20.4f   %.4f\n",
           Str(e), o1, oe, TW[j], TWsec3[j], th[oe], TN[j]));
  \\ (a) omega1 by (7) agrees with LS's (commented-out) omega1 row in all 7 columns
  check(O1 == TO1, "E136(5a): omega1 of (7) = LS's row 15,49,72,129,176,566,6458");
  \\ (b) omega_eps agrees in 5 columns; eps=1/2 gives 128 (LS 127), eps=1/3 gives 6016 (LS 6458)
  check(OE == [14, 49, 72, 128, 175, 548, 6016], "E136(5b): omega_eps = 14,49,72,128,175,548,6016");
  ok = (lngamma(128) + th[127]/2 - 127*log(th[127]) - log(sqrt(2*Pi*127)) < -0.2);
  check(ok, "E136(5b): LS's omega_{1/2} = 127 violates (8) at i = 127 (margin < -0.2)");
  \\ (c) N_eps = Theta(p_{omega_eps}) matches LS to their printed digits for 3/4, 7/12, 5/12,
  \\     and for 1/2 at LS's own omega = 127; 34/71 is 1004.7623, printed 1004.763 (last digit
  \\     off by 7e-4); not at all for 6/11 (theta(p_72) = 335.07, LS print 335.71)
  ok = (abs(th[14] - 37.1101) < 5e-5 && abs(th[49] - 204.75) < 5e-3 && abs(th[175] - 1004.763) < 1e-3 && abs(th[175] - 1004.7623) < 5e-5
        && abs(th[548] - 3894.57) < 5e-3 && abs(th[127] - 679.585) < 5e-4 && abs(th[72] - 335.07) < 5e-3);
  check(ok, "E136(5c): LS's N_eps = e^theta(p_omega) in 5 columns; 6/11 prints 335.71 for 335.07");
  \\ (d) eps = 1/3: e^63727 is Robin's lower bound 6458*X0(6458), not Theta(p_6458) = e^64243.3
  printf("  eps=1/3: 6458*X0(6458) = %.4f;  theta(p_6458) = %.4f;  theta(p_6460) = %.4f\n",
         6458*X0(6458), th[6458], th[6460]);
  check(abs(6458*X0(6458) - 63727) < 0.5 && th[6458] > 64243, "E136(5d): LS's N_{1/3} = e^{6458 X0(6458)} (Robin), not Theta(p_6458)");
  return(0);
};

\\ ---------------------------------------------------------------- (6)
lsroute() = {
  my(e = 2/13, o1, LN, Lam2);
  print("### (6) comparison: [LS12]'s own route with eps = 2/13 (float estimate, [E]) ###");
  \\ omega1 by (7); omega_{2/13} <= omega1, and N_eps = Theta(p_{omega_eps}) cannot be
  \\ computed exactly at this size; estimate log N_eps ~ omega1 * X0(omega1) (Robin, a lower
  \\ bound for theta(p_{omega1})), then log|b| < (7/12) log N_eps + log(4)/3 from c < N^{7/4}.
  my(lo = 1000, hi = 10^15);
  while(hi - lo > 1, my(m = (lo + hi) \ 2); if(e*X0(m) - log(X0(m)) >= 1, hi = m, lo = m));
  o1 = hi;
  LN = o1*X0(o1);
  Lam2 = (7/12)*LN + log(4)/3;
  printf("  omega1(2/13) = %.4e,  log N_{2/13} ~ %.4e,  route bound log|b| < ~%.4e\n", o1, LN, Lam2);
  return([o1, LN, Lam2]);
};

run() = {
  my(r);
  default(realprecision, 80);
  tier1();
  print();
  tier1star();
  print();
  constants();
  print();
  r = threshold();
  print();
  lstable();
  print();
  my(s = lsroute());
  printf("  ratio (LS route)/(ours) = %.3f\n", s[3]/r[3]);
  printf("\nE136 GATE: %s   (%d failures)\n", if(FAIL, "*** RED ***", "GREEN"), FAIL);
  if(FAIL, quit(1));
  return(0);
};

run();
