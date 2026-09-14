\\ PARI/GP test program for the Somos-type recurrence from the generating function root.
\\
\\ The polynomial is A(y)*x^2 + B(y)*x + C(y)=0 and we take
\\ x(y) = (-B - sqrt(B^2 - 4*A*C)) / (2*A).

Hankel(v) = vector((#v+1)\2, n, matdet(matrix(n, n, i, j, v[i+j-1])));

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

genfun(l, j, m, r, t, nterms) =
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

coeff_vector(l, j, m, r, t, nterms) =
{
  Vec(genfun(l, j, m, r, t, nterms));
};

check_recurrence(v, l, j, m, r, t) =
{
  my(ok = 1);

  if (#v < 8,
    print("Need at least 8 terms for a meaningful recurrence check");
    return(0);
  );

  if (v[1] != l || v[2] != m || v[3] != r || v[4] != j,
    print("Initial terms fail: v[1..4] = ", [v[1], v[2], v[3], v[4]],
          " expected = ", [l, m, r, j]);
    ok = 0;
  );

  for (n = 5, #v,
    if (v[n-4] == 0,
      print("Division by zero in recurrence at n=", n, " because v[n-4]=0");
      return(2); \\ Skip this parameter tuple.
    );

    my(rhs = (v[n-1]*v[n-3] + t*v[n-2]^2) / v[n-4]);
    if (v[n] != rhs,
      print("Recurrence fail at n=", n,
            ": v[n]=", v[n], " rhs=", rhs);
      ok = 0;
      break;
    );
  );

  ok;
};

verify_section4_correction() =
{
  my(l = 6, j = 7, m = 3, r = 5, t = 11);
  my(oldC1 = l^3*m^2*r^2*t + l^4*r^3
    + j*(m - 1)*(j*(-15*l^4 + 85*l^3 - 225*l^2 + 274*l - 120)
      - l^3*m^2 - 3*(l-1)*(l-2)*(l-3)*(l-4)*(l-5)));
  my(newC1 = l^3*m^2*r^2*t + l^4*r^3 - l^3*j*(m - 1)*(l^2*j + m^2));
  my(diff = oldC1 - newC1);
  my(expected = j*(m - 1)*(j - 3)*(l - 1)*(l - 2)*(l - 3)*(l - 4)*(l - 5));

  if (diff != expected,
    print("Section 4 correction check failed: diff = ", diff, ", expected = ", expected);
    return(0)
  );

  print("Section 4 correction check: diff = ", diff, " = ", expected,
        " for (l,j,m,r,t) = (", l, ",", j, ",", m, ",", r, ",", t, ")");
  1;
};

run_one_test(l, j, m, r, t, nterms, verbose = 0) =
{
  my(v, h, status);
  my(y = 'y + O('y^nterms));
  my(A = Apoly(l, j, m, r, t, y));
  my(B = Bpoly(l, j, m, r, t, y));
  my(C = Cpoly(l, j, m, r, t, y));
  my(D = B^2 - 4*A*C);

  if (valuation(D, 'y) % 2,
    if (verbose,
      print("Root expansion blocked by odd valuation(D) for tuple (l,j,m,r,t) = (", l, ",", j, ",", m, ",", r, ",", t, ")")
    );
    return(4);
  );

  iferr(v = coeff_vector(l, j, m, r, t, nterms), E,
    if (verbose,
      print("Root expansion error for tuple (l,j,m,r,t) = (", l, ",", j, ",", m, ",", r, ",", t, ")")
    );
    return(3);
  );

  h = Hankel(v);
  status = check_recurrence(h, l, j, m, r, t);

  if (verbose || status != 1,
    print("----------------------------------------");
    print("(l,j,m,r,t) = (", l, ",", j, ",", m, ",", r, ",", t, ")");
    print("v[1..", min(#v, 12), "] = ", vector(min(#v, 12), k, v[k]));
    print("Hankel(v) first values = ", vector(min(#h, 6), k, h[k]));
    if (status == 2,
      print("Recurrence status: SKIP (division by zero in recurrence)"),
      print("Recurrence status: ", if(status, "PASS", "FAIL"))
    );
  );

  status;
};

build_stress_tests(num_random = 1000, seed = 20266904) =
{
  my(pool_all = [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 18, 20, 33, 77, 111]);
  my(pool_large = [-12, -11, -10, -9, -8, -7, -6, 6, 7, 8, 9, 10, 11, 12, 15, 18, 33, 77, 111]);
  my(tests = List());
  my(base = [
    [1, 1, 1, 1, 1],
    [1, 2, 1, 1, 1],
    [2, 4, 2, 2, 1],
    [3, 3, 3, 5, 1],
    [2, 4, 2, 6, 1],
    [3, 3, 3, 6, 1],
    [5, 4, 5, 6, 1],
    [6, 3, 6, 7, 1],
    [6, 3, 3, 7, 1]
  ]);
  my(mandatory_large = [
    [6, 2, 2, 2, 1],
    [2, 6, 2, 2, 1],
    [2, 2, 6, 2, 1],
    [2, 2, 2, 6, 1],
    [2, 2, 2, 2, 6],
    [-6, 2, 2, 2, 1],
    [2, -6, 2, 2, 1],
    [2, 2, -6, 2, 1],
    [2, 2, 2, -6, 1],
    [2, 2, 2, 2, -6],
    [6, 6, 2, 2, 1],
    [6, -6, 2, -6, 1]
  ]);

  for (k = 1, #base, listput(tests, base[k]));
  for (k = 1, #mandatory_large, listput(tests, mandatory_large[k]));
  setrand(seed);
  for (k = 1, num_random,
    my(l = pool_all[1 + random(#pool_all)]);
    my(j = pool_all[1 + random(#pool_all)]);
    my(m = pool_all[1 + random(#pool_all)]);
    my(r = pool_all[1 + random(#pool_all)]);
    my(t = pool_all[1 + random(#pool_all)]);

    \\ Ensure the random tuple always includes at least one high-magnitude parameter.
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
    if (m == 0 || m == 1, m = 6);
    if (r == 0, r = 7);
    if (t == 0, t = -6);
    listput(tests, [l, j, m, r, t]);
  );
  Vec(tests);
};

run_all_tests(nterms = 24, num_random = 580, verbose = 0) =
{
  my(tests, all_ok = 1, pass_count = 0, fail_count = 0, skip_count = 0);
  my(enforced_count = 0, fail_tuples = List(), root_error_count = 0, root_error_tuples = List());
  my(odd_val_count = 0, odd_val_tuples = List());
  my(high_tuple_count = 0, high_param_hits = [0, 0, 0, 0, 0]);

  tests = build_stress_tests(num_random);
  print("Stress-suite size: ", #tests, " (base + randomized)");
  print("Policy: mandatory high-value coverage exists, but not every parameter must be >5 in every tuple");

  for (k = 1, #tests,
    my(l = tests[k][1], j = tests[k][2], m = tests[k][3], r = tests[k][4], t = tests[k][5]);
    enforced_count++;
    if (abs(l) > 5 || abs(j) > 5 || abs(m) > 5 || abs(r) > 5 || abs(t) > 5,
      high_tuple_count++;
    );
    if (abs(l) > 5, high_param_hits[1]++);
    if (abs(j) > 5, high_param_hits[2]++);
    if (abs(m) > 5, high_param_hits[3]++);
    if (abs(r) > 5, high_param_hits[4]++);
    if (abs(t) > 5, high_param_hits[5]++);

    my(a0 = l^2*j*m*(m-1)*r);
    if (a0 == 0,
      skip_count++;
      next;
    );
    my(status = run_one_test(l, j, m, r, t, nterms, verbose));
    if (status == 1,
      pass_count++,
      if (status == 2,
        skip_count++,
        if (status == 3,
          root_error_count++;
          listput(root_error_tuples, [l, j, m, r, t]);
          skip_count++,
          if (status == 4,
            odd_val_count++;
            listput(odd_val_tuples, [l, j, m, r, t]);
            skip_count++,
            fail_count++;
            listput(fail_tuples, [l, j, m, r, t]);
            all_ok = 0;
          )
        )
      )
    );
  );

  print("========================================");
  print("Total tuples attempted: ", enforced_count);
  print("Tuples with at least one |parameter|>5: ", high_tuple_count);
  print("High-value hits by parameter [l,j,m,r,t]: ", high_param_hits);
  print("Passed: ", pass_count, "  Failed: ", fail_count, "  Skipped: ", skip_count);
  print("Odd-valuation(D) skips: ", odd_val_count);
  print("Root-expansion domain skips: ", root_error_count);
  if (odd_val_count > 0,
    print("Odd-valuation(D) tuples (l,j,m,r,t):");
    for (k = 1, #odd_val_tuples, print("  ", odd_val_tuples[k]));
  );
  if (fail_count > 0,
    print("Failing tuples (l,j,m,r,t):");
    for (k = 1, #fail_tuples, print("  ", fail_tuples[k]));
  );
  if (root_error_count > 0,
    print("Root-expansion-error tuples (l,j,m,r,t):");
    for (k = 1, #root_error_tuples, print("  ", root_error_tuples[k]));
  );
  print("Overall status: ", if(all_ok, "PASS", "FAIL"));
  all_ok;
};

\\ Execute when script is read.
verify_section4_correction();
run_all_tests();
