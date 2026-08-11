/* Verification of the basic setup (Prop. 2.1 and Lemma 2.2 of the paper) for
   f_b(x) = x^3 - 3 b x - b^3, eps = theta - (b+1).
   Checks: disc(f), D_K, index, |D_K|/b^6, min poly of eps and of eta=-1/eps,
   real embedding sizes. */

verify(b) = {
  my(f, g, nf, df, dK, idx, eps_emb, theta, roots, eta_emb);
  f = x^3 - 3*b*x - b^3;
  if(!polisirreducible(f), printf("b=%d reducible\n", b); return);
  nf = nfinit(f);
  df = poldisc(f);
  dK = nf.disc;
  idx = sqrtint(df/dK);   /* df, dK both negative; ratio positive */
  /* min poly of eps = theta-(b+1): g(x)=f(x+(b+1)) */
  g = subst(f, x, x + (b+1));
  /* real root theta of f */
  roots = polrootsreal(f);
  theta = roots[1];   /* the unique real root */
  eps_emb = theta - (b+1);
  eta_emb = -1/eps_emb;
  printf("b=%4d | discf=%s | D_K=%s | index=%s = %s\n",
         b, df, dK, idx, factor(idx));
  printf("        b^3-4 = %s = %s%s\n", b^3-4, factor(b^3-4),
         if(issquarefree(b^3-4), " [squarefree]", ""));
  printf("        |D_K|/b^6 = %.4f | eps_emb=%.6g | eta=-1/eps=%.6g (~b^2=%d)\n",
         abs(dK)/b^6*1.0, eps_emb, eta_emb, b^2);
  printf("        g(x)=%s ; expect const term 1, x^2 coeff 3(b+1)=%d, x coeff 3(b^2+b+1)=%d\n",
         g, 3*(b+1), 3*(b^2+b+1));
};

print("=== non-exceptional b (3 nmid b, b^3-4 squarefree) ===");
for(b=4, 50, if(b%3!=0 && issquarefree(b^3-4), verify(b)));
print();
print("=== exceptional b ===");
foreach([3,5,9,96,112,1425,1485], b, verify(b));
\q
