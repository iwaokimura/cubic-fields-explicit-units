\\ check-prime-stats.gp -- verifies the numerical Remark after Cor. 4.7 of the
\\ paper (squarefree statistics of p^3 -+ 4 over primes 5 <= p < 20000, and the
\\ heuristic density prod_q (1 - rho(q)/(q^2-q)) = 0.926485...).
\\
\\ Claims checked (E122):
\\   (a) there are exactly 2260 primes p with 5 <= p < 20000;
\\   (b) exactly 2102 of them have p^3 - 4 squarefree (93.0%);
\\   (c) exactly 2094 of them have p^3 + 4 squarefree (92.7%);
\\   (d) rho(q) is the same for the two signs (checked for q <= 10^4);
\\   (e) the partial product over q <= 2*10^7, with the crude tail bound
\\       prod_{q > Q} (1 - rho/(q^2-q)) >= 1 - 3/Q (valid since rho <= 3 and
\\       sum_{n > Q} 1/(n(n-1)) = 1/Q), brackets a value whose decimal
\\       expansion begins 0.926485.
\\ The density check is floating point, so the whole gate is [E]-grade.
\\
\\ Usage: gp -q check-prime-stats.gp < /dev/null

default(parisize, 256*10^6);

nfail = 0;

check(c, msg) = {
  if(c,
    print("ok   ", msg),
    nfail++; print("FAIL ", msg));
  return(c);
};

\\ rho(q, c) = #{ x in (Z/q^2 Z)^* : x^3 == c (mod q^2) }, for c = +-4.
\\ For q >= 5 Hensel lifting is unique (q does not divide 3x), so this equals
\\ the number of roots of x^3 - c mod q: one root if q = 2 (mod 3), and
\\ 3 or 0 according as c is a cube mod q if q = 1 (mod 3).
rho(q, c) = {
  my(n);
  if(q <= 3,
    n = 0;
    for(x = 1, q^2,
      if(gcd(x, q) == 1 && Mod(x, q^2)^3 == Mod(c, q^2), n++));
    return(n));
  if(q % 3 == 2, return(1));
  return(if(Mod(c, q)^((q-1)/3) == 1, 3, 0));
};

countprimes() = {
  my(n = 0);
  forprime(p = 5, 19999, n++);
  return(n);
};

sqfreecounts() = {
  my(aminus = 0, aplus = 0);
  forprime(p = 5, 19999,
    if(issquarefree(p^3 - 4), aminus++);
    if(issquarefree(p^3 + 4), aplus++));
  return([aminus, aplus]);
};

rhosymmetric() = {
  my(ok = 1);
  forprime(q = 2, 10^4,
    if(rho(q, 4) != rho(q, -4), ok = 0));
  return(ok);
};

density(Q) = {
  my(P = 1.0);
  forprime(q = 2, Q,
    P *= 1 - rho(q, 4)/(q^2 - q));
  return(P);
};

run() = {
  my(np, cnts, PQ, Q = 2*10^7, lo, hi);
  np = countprimes();
  check(np == 2260, Strprintf("(a) #primes in [5,20000) = %d (claim 2260)", np));
  cnts = sqfreecounts();
  check(cnts[1] == 2102, Strprintf("(b) #{p^3-4 squarefree} = %d (claim 2102)", cnts[1]));
  check(cnts[2] == 2094, Strprintf("(c) #{p^3+4 squarefree} = %d (claim 2094)", cnts[2]));
  check(round(1000*cnts[1]/np) == 930, "(b') percentage rounds to 93.0");
  check(round(1000*cnts[2]/np) == 927, "(c') percentage rounds to 92.7");
  check(rhosymmetric(), "(d) rho(q,4) = rho(q,-4) for all q <= 10^4");
  PQ = density(Q);
  lo = PQ * (1 - 3/Q);  \\ crude tail bound: each omitted factor >= 1 - 3/(q^2-q)
  hi = PQ;
  printf("     partial product over q <= %d: %.9f, interval [%.9f, %.9f]\n",
         Q, PQ, lo, hi);
  check(floor(lo*10^6) == 926485 && floor(hi*10^6) == 926485,
        "(e) density interval truncates to 0.926485");
  print(if(nfail == 0, "E122 GATE: GREEN (0 failures)",
        Strprintf("E122 GATE: RED (%d failures)", nfail)));
  return(nfail);
};

run();
