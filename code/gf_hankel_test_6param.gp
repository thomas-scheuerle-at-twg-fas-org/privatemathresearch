\\ PARI/GP test program for the six-parameter extension from
\\ six_parameter_somos4_followup_v0_3.tex.
\\
\\ The input order matches the existing tester:
\\   (l, j, m, r, alpha, t, q)
\\ where the initial Hankel data are [H_1,H_2,H_3,H_4] = [l,m,r,j],
\\ alpha is the first Somos-4 coefficient, tau=t is the second,
\\ and q is a chosen sixth root with q^6 = alpha.

Hankel(v) = vector((#v+1)\2, n, matdet(matrix(n, n, i, j, v[i+j-1])));
ShiftedHankel(v) = vector(#v\2, n, matdet(matrix(n, n, i, j, v[i+j])));

Apoly(l, j, m, r, t, y) =
{
  l*j*m*r^2*(t - j)*y^3
  + r*(-(l^2*j*m + m^2*(m + r^2))*t
       + (2*m - 1)*l^2*j^2 + j*m^2*(m + r^2) - l*r*(m + r^2))*y^2
  + l*(m^2*r^2*t - (m - 1)*l^2*j^2
       - m*(m^2 + 2*m*r^2 - m - r^2)*j + l*r^3)*y
  + l^2*j*m*(m - 1)*r;
};

Bpoly(l, j, m, r, t, y) =
{
  (-l^2*j*m*r^2*t)*y^3
  + r*((2*l^3*j*m + l*m^2*(2*m + r^2))*t
       - (2*m - 1)*l^3*j^2 - l*j*m^3 + l^2*r*(2*m + r^2))*y^2
  + l^2*(-2*m^2*r^2*t + 2*(m - 1)*l^2*j^2
        + m*(2*m^2 + 2*m*r^2 - 2*m - r^2)*j - 2*l*r^3)*y
  + (-2*l^3*j*m*(m - 1)*r);
};

Cpoly(l, j, m, r, t, y) =
{
  -l^2*m*r*(t*(l^2*j + m^2) + l*r)*y^2
  + (l^3*m^2*r^2*t + l^4*r^3
     - l^3*j*(m - 1)*(l^2*j + m^2))*y
  + l^4*j*m*(m - 1)*r;
};

five_genfun(l, j, m, r, t, nterms) =
{
  my(y = 'y + O('y^nterms));
  my(A = Apoly(l, j, m, r, t, y));
  my(B = Bpoly(l, j, m, r, t, y));
  my(C = Cpoly(l, j, m, r, t, y));
  my(S = sqrt(B^2 - 4*A*C));
  my(root_minus, root_plus);

  if (polcoeff(A, 0) == 0,
    root_minus = -2*C / (B - S);
    root_plus = -2*C / (B + S),
    root_minus = (-B - S) / (2*A);
    root_plus = (-B + S) / (2*A)
  );
  my(vminus = Vec(root_minus));
  my(vplus = Vec(root_plus));
  my(hminus = Hankel(vminus));
  my(hplus = Hankel(vplus));

  if (#hminus >= 4 && hminus[1] == l && hminus[2] == m && hminus[3] == r && hminus[4] == j,
    return(root_minus)
  );
  if (#hplus >= 4 && hplus[1] == l && hplus[2] == m && hplus[3] == r && hplus[4] == j,
    return(root_plus)
  );

  if (r == 1,
    root_minus,
    root_plus
  );
};

five_coeff_vector(l, j, m, r, t, nterms) =
{
  Vec(five_genfun(l, j, m, r, t, nterms));
};

transported_parameters(l, j, m, r, alpha, t, q) =
{
  if (q == 0, error("Need q != 0 for the six-parameter transport"));
  if (q^6 != alpha, error("Need q^6 = alpha"));
  [l, j/q^12, m/q^2, r/q^6, t/q^8];
};

six_coeff_vector(l, j, m, r, alpha, t, q, nterms) =
{
  my(primed = transported_parameters(l, j, m, r, alpha, t, q));
  my(base = five_coeff_vector(primed[1], primed[2], primed[3], primed[4], primed[5], nterms));
  vector(#base, n, q^(n-1)*base[n]);
};

check_recurrence6(h, l, j, m, r, alpha, t) =
{
  my(ok = 1);

  if (#h < 8,
    print("Need at least 8 Hankel values for a meaningful recurrence check");
    return(0);
  );

  if (h[1] != l || h[2] != m || h[3] != r || h[4] != j,
    print("Initial Hankel values fail: h[1..4] = ", [h[1], h[2], h[3], h[4]],
          " expected = ", [l, m, r, j]);
    ok = 0;
  );

  if (h[5] != (alpha*j*m + t*r^2) / l,
    print("Low-order check fail at H_5: computed = ", h[5],
          " expected = ", (alpha*j*m + t*r^2) / l);
    ok = 0;
  );
  if (h[6] != (alpha*h[5]*r + t*j^2) / m,
    print("Low-order check fail at H_6: computed = ", h[6],
          " expected = ", (alpha*h[5]*r + t*j^2) / m);
    ok = 0;
  );

  for (n = 5, #h,
    if (h[n-4] == 0,
      print("Division by zero in recurrence at n=", n, " because h[n-4]=0");
      return(2);
    );

    my(rhs = (alpha*h[n-1]*h[n-3] + t*h[n-2]^2) / h[n-4]);
    if (h[n] != rhs,
      print("Recurrence fail at n=", n,
            ": h[n]=", h[n], " rhs=", rhs);
      ok = 0;
      break;
    );
  );

  ok;
};

check_graded_companion(v, h, q) =
{
  my(d = ShiftedHankel(v));
  my(ok = 1);
  my(limit = min(#d, #h - 2));

  for (n = 1, limit,
    my(rhs = h[n+2] / q^(3*n + 2));
    if (d[n] != rhs,
      print("Graded companion fail at N=", n,
            ": D_N=", d[n], " expected=", rhs);
      ok = 0;
      break;
    );
  );

  ok;
};

verify_alpha_one_specialization() =
{
  my(l = 2, j = 5, m = 3, r = 7, t = 11, q = 1, alpha = 1, nterms = 18);
  my(vfive = five_coeff_vector(l, j, m, r, t, nterms));
  my(vsix = six_coeff_vector(l, j, m, r, alpha, t, q, nterms));

  if (vfive != vsix,
    print("alpha=1 specialization check failed");
    return(0);
  );

  print("alpha=1 specialization check: PASS");
  1;
};

run_one_test6(l, j, m, r, alpha, t, q, nterms, verbose = 0) =
{
  my(primed, y, A, B, C, D, v, h, status, companion_ok);

  if (l == 0 || j == 0 || m == 0 || r == 0 || m == q^2,
    if (verbose,
      print("Transport skip: primed constant term A(0) vanishes for tuple (l,j,m,r,alpha,t,q) = (",
            l, ",", j, ",", m, ",", r, ",", alpha, ",", t, ",", q, ")")
    );
    return(5);
  );

  primed = transported_parameters(l, j, m, r, alpha, t, q);
  y = 'y + O('y^nterms);
  A = Apoly(primed[1], primed[2], primed[3], primed[4], primed[5], y);
  B = Bpoly(primed[1], primed[2], primed[3], primed[4], primed[5], y);
  C = Cpoly(primed[1], primed[2], primed[3], primed[4], primed[5], y);
  D = B^2 - 4*A*C;

  if (valuation(D, 'y) % 2,
    if (verbose,
      print("Root expansion blocked by odd valuation(D) for tuple (l,j,m,r,alpha,t,q) = (",
            l, ",", j, ",", m, ",", r, ",", alpha, ",", t, ",", q, ")")
    );
    return(4);
  );

  iferr(v = six_coeff_vector(l, j, m, r, alpha, t, q, nterms), E,
    if (verbose,
      print("Root expansion error for tuple (l,j,m,r,alpha,t,q) = (",
            l, ",", j, ",", m, ",", r, ",", alpha, ",", t, ",", q, ")")
    );
    return(3);
  );

  h = Hankel(v);
  status = check_recurrence6(h, l, j, m, r, alpha, t);
  companion_ok = check_graded_companion(v, h, q);
  if (!companion_ok, status = 0);

  if (verbose || status != 1,
    my(d = ShiftedHankel(v));
    print("----------------------------------------");
    print("(l,j,m,r,alpha,t,q) = (", l, ",", j, ",", m, ",", r, ",", alpha, ",", t, ",", q, ")");
    print("v[1..", min(#v, 12), "] = ", vector(min(#v, 12), k, v[k]));
    print("Hankel(v) first values = ", vector(min(#h, 8), k, h[k]));
    print("ShiftedHankel(v) first values = ", vector(min(#d, 6), k, d[k]));
    if (status == 2,
      print("Recurrence status: SKIP (division by zero in recurrence)"),
      print("Recurrence status: ", if(status, "PASS", "FAIL"))
    );
    print("Graded companion status: ", if(companion_ok, "PASS", "FAIL"));
  );

  if (status == 1 && companion_ok,
    1,
    status
  );
};

build_stress_tests6(num_random = 240, seed = 20266918) =
{
  my(pool_all = [-12, -11, -10, -8, -7, -6, -5, -4, -3, -2, -1, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 15, 18, 20, 33]);
  my(pool_large = [-12, -11, -10, -8, -7, -6, 6, 7, 8, 10, 11, 12, 15, 18, 20, 33]);
  my(q_pool = [1, 2, 3, -1, -2, -3]);
  my(tests = List());
  my(base = [
    [2, 5, 3, 7, 1, 11],
    [3, 7, 2, 5, 2, 3],
    [5, 6, 8, 11, 2, 7],
    [7, 10, 5, 9, 3, 4],
    [6, 5, 3, 8, -2, 9],
    [10, 7, 5, 6, -3, 2]
  ]);

  for (k = 1, #base, listput(tests, base[k]));
  setrand(seed);
  for (k = 1, num_random,
    my(l = pool_all[1 + random(#pool_all)]);
    my(j = pool_all[1 + random(#pool_all)]);
    my(m = pool_all[1 + random(#pool_all)]);
    my(r = pool_all[1 + random(#pool_all)]);
    my(q = q_pool[1 + random(#q_pool)]);
    my(t = pool_all[1 + random(#pool_all)]);

    if (abs(l) <= 5 && abs(j) <= 5 && abs(m) <= 5 && abs(r) <= 5 && abs(t) <= 5,
      my(pos = 1 + random(5));
      my(vbig = pool_large[1 + random(#pool_large)]);
      if (pos == 1, l = vbig);
      if (pos == 2, j = vbig);
      if (pos == 3, m = vbig);
      if (pos == 4, r = vbig);
      if (pos == 5, t = vbig);
    );

    if (l == 0, l = 6);
    if (j == 0, j = -6);
    if (m == 0 || m == q^2, m = q^2 + 2);
    if (r == 0, r = 7);
    if (t == 0, t = -6);
    listput(tests, [l, j, m, r, q, t]);
  );
  Vec(tests);
};

run_all_tests6(nterms = 24, num_random = 240, verbose = 0) =
{
  my(tests, all_ok = 1, pass_count = 0, fail_count = 0, skip_count = 0);
  my(domain_skip_count = 0, domain_skip_tuples = List());
  my(root_error_count = 0, root_error_tuples = List());
  my(odd_val_count = 0, odd_val_tuples = List());
  my(recurrence_skip_count = 0, recurrence_skip_tuples = List());

  tests = build_stress_tests6(num_random);
  print("Six-parameter stress-suite size: ", #tests, " (base + randomized)");
  print("Transport model: test the q-lifted branch with explicit q and alpha=q^6");

  for (k = 1, #tests,
    my(l = tests[k][1], j = tests[k][2], m = tests[k][3], r = tests[k][4]);
    my(q = tests[k][5], t = tests[k][6], alpha = q^6);
    my(status = run_one_test6(l, j, m, r, alpha, t, q, nterms, verbose));
    if (status == 1,
      pass_count++,
      if (status == 2,
        recurrence_skip_count++;
        skip_count++;
        listput(recurrence_skip_tuples, [l, j, m, r, alpha, t, q]),
        if (status == 3,
          root_error_count++;
          skip_count++;
          listput(root_error_tuples, [l, j, m, r, alpha, t, q]),
          if (status == 4,
            odd_val_count++;
            skip_count++;
            listput(odd_val_tuples, [l, j, m, r, alpha, t, q]),
            if (status == 5,
              domain_skip_count++;
              skip_count++;
              listput(domain_skip_tuples, [l, j, m, r, alpha, t, q]),
              fail_count++;
              listput(root_error_tuples, [l, j, m, r, alpha, t, q]);
              all_ok = 0;
            )
          )
        )
      )
    );
  );

  print("========================================");
  print("Passed: ", pass_count, "  Failed: ", fail_count, "  Skipped: ", skip_count);
  print("Primed-domain skips: ", domain_skip_count);
  print("Odd-valuation(D) skips: ", odd_val_count);
  print("Root-expansion skips: ", root_error_count);
  print("Recurrence division-by-zero skips: ", recurrence_skip_count);
  if (domain_skip_count > 0,
    print("Primed-domain skip tuples (l,j,m,r,alpha,t,q):");
    for (k = 1, #domain_skip_tuples, print("  ", domain_skip_tuples[k]));
  );
  if (odd_val_count > 0,
    print("Odd-valuation(D) tuples (l,j,m,r,alpha,t,q):");
    for (k = 1, #odd_val_tuples, print("  ", odd_val_tuples[k]));
  );
  if (root_error_count > 0,
    print("Root-expansion-error tuples (l,j,m,r,alpha,t,q):");
    for (k = 1, #root_error_tuples, print("  ", root_error_tuples[k]));
  );
  if (recurrence_skip_count > 0,
    print("Recurrence-division-by-zero tuples (l,j,m,r,alpha,t,q):");
    for (k = 1, #recurrence_skip_tuples, print("  ", recurrence_skip_tuples[k]));
  );
  print("Overall status: ", if(all_ok, "PASS", "FAIL"));
  all_ok;
};

\\ Execute when script is read.
verify_alpha_one_specialization();
run_all_tests6();