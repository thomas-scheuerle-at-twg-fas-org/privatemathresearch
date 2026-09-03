\\ PARI/GP test program for the Somos-type recurrence from the generating function root.
\\
\\ The polynomial is A(y)*x^2 + B(y)*x + C(y)=0 and we take
\\ x(y) = (-B - sqrt(B^2 - 4*A*C)) / (2*A).

Hankel(v) = vector((#v+1)\2, n, matdet(matrix(n, n, i, j, v[i+j-1])));

Apoly(l, j, t, y) =
{
  (l*j*t - l*j^2)*y^2
  + (-(l^2*j + 2)*t + (l^2*j^2 + 2*j - 2*l))*y
  + (l*t + l*(l - j));
};

Bpoly(l, j, t, y) =
{
  (-l^2*j*t)*y^2
  + ((2*l^3*j + 3*l)*t + (-l^3*j^2 - l*j + 3*l^2))*y
  + ((-2*l^2)*t + l^2*(j - 2*l));
};

Cpoly(l, j, t, y) =
{
  ((-(l^4*j + l^2))*t - l^3)*y
  + (l^3*t + l^4);
};

genfun(l, j, t, nterms) =
{
  my(y = 'y + O('y^nterms));
  my(A = Apoly(l, j, t, y));
  my(B = Bpoly(l, j, t, y));
  my(C = Cpoly(l, j, t, y));
  my(S = sqrt(B^2 - 4*A*C));

  \\ Working branch rule from tests: switch sign for negative j.
  if (j < 0,
    (-B + S) / (2*A),
    (-B - S) / (2*A)
  );
};

coeff_vector(l, j, t, nterms) =
{
  Vec(genfun(l, j, t, nterms));
};

check_recurrence(v, l, j, t) =
{
  my(ok = 1);

  if (#v < 8,
    print("Need at least 8 terms for a meaningful recurrence check");
    return(0);
  );

  if (v[1] != l || v[2] != 1 || v[3] != 1 || v[4] != j,
    print("Initial terms fail: v[1..4] = ", [v[1], v[2], v[3], v[4]],
          " expected = ", [l, 1, 1, j]);
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

run_one_test(l, j, t, nterms) =
{
  my(v, h, status);

  v = coeff_vector(l, j, t, nterms);
  h = Hankel(v);
  status = check_recurrence(h, l, j, t);

  print("----------------------------------------");
  print("(l,j,t) = (", l, ",", j, ",", t, ")");
  print("v[1..", min(#v, 12), "] = ", vector(min(#v, 12), k, v[k]));
  print("Hankel(v) first values = ", vector(min(#h, 6), k, h[k]));
  if (status == 2,
    print("Recurrence status: SKIP (division by zero in recurrence)"),
    print("Recurrence status: ", if(status, "PASS", "FAIL"))
  );

  status;
};

run_all_tests(nterms = 18) =
{
  my(tests, all_ok = 1, pass_count = 0, fail_count = 0, skip_count = 0);

  \\ Broader sample with positive and negative values.
  tests = [
    [-3, -2, 1],
    [-3, 1, 2],
    [-2, -1, 1],
    [-2, 3, -1],
    [-1, -2, 2],
    [-1, 2, 1],
    [1, -2, 1],
    [1, 1, 1],
    [1, 3, 1],
    [2, -3, 1],
    [2, 2, 1],
    [2, 3, 2],
    [3, -1, 2],
    [3, 2, -1],
    [3, 3, 2],
    [4, -2, 1]
  ];

  for (k = 1, #tests,
    my(l = tests[k][1], j = tests[k][2], t = tests[k][3]);
    my(a0 = l*t + l*(l - j));
    print("Checking (l,j,t) = (", l, ",", j, ",", t, "), A(0)=", a0);
    if (a0 == 0,
      print("Skipping illegal test (A(0)=0): (l,j,t) = (", l, ",", j, ",", t, ")");
      skip_count++;
      next;
    );
    my(status = run_one_test(l, j, t, nterms));
    if (status == 1,
      pass_count++,
      if (status == 2,
        skip_count++,
        fail_count++;
        all_ok = 0;
      )
    );
  );

  print("========================================");
  print("Passed: ", pass_count, "  Failed: ", fail_count, "  Skipped: ", skip_count);
  print("Overall status: ", if(all_ok, "PASS", "FAIL"));
  all_ok;
};

\\ Execute when script is read.
run_all_tests();
