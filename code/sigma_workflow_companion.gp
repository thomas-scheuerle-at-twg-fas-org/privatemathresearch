\\ PARI/GP companion for the algebraic-to-sigma workflow of Somos--4 data.
\\ This script implements the geometric normalization described in the draft
\\ "From Direct Algebraic Generating Functions to Elliptic Sigma and Theta
\\ Representations of Somos--4 Sequences".
\\
\\ The functions below are deliberately written in a way that separates the
\\ exact algebraic checks from the numerical elliptic analysis.  This makes the
\\ script useful both as a verification tool and as a scientific appendix that
\\ remains human-readable.

\\ ---------------------------------------------------------------------------
\\ Basic Somos data and the first invariant J
\\ ---------------------------------------------------------------------------

somos_J(lambda, m, r, eta, tau) =
{
  lambda*eta/(m*r)
  + m^2/(lambda*r)
  + r^2/(m*eta)
  + tau*m*r/(lambda*eta);
};

quartic_poly(J, tau, X) = (X^2 - J*X + tau)^2 - 4*X;

quadric_recurrence(x, y, tau) =
{
  y = y;
  [y, (y + tau)/(x*y^2)];
};

somos_recurrence_step(v, tau) =
{
  my(n = #v);
  if (n < 4,
    error("Need at least four values to advance the Somos-4 orbit")
  );
  if (v[n-3] == 0,
    error("Zero denominator in Somos-4 recurrence")
  );
  (v[n-1]*v[n-3] + tau*v[n-2]^2) / v[n-3];
};

somos_orbit(lambda, m, r, eta, tau, N) =
{
  my(v = [lambda, m, r, eta]);
  for (n = 5, N,
    listput(v, somos_recurrence_step(v, tau));
  );
  v;
};

\\ ---------------------------------------------------------------------------
\\ Quartic-to-Weierstrass normalization
\\ ---------------------------------------------------------------------------

quartic_to_weierstrass(X, Y, J, tau) =
{
  my(U = (Y + X^2 - J*X + tau)/2);
  my(V = U*(2*X - J) - 1);
  my(u = U + (J^2 - 4*tau)/12);
  [u, V];
};

weierstrass_to_quartic(u, v, J, tau) =
{
  my(U = u - (J^2 - 4*tau)/12);
  if (U == 0,
    error("Affine inverse map hits the excluded U = 0 chart")
  );
  my(X = (v + J*U + 1)/(2*U));
  my(Y = 2*U - X^2 + J*X - tau);
  [X, Y];
};

weierstrass_invariants(J, tau) =
{
  my(a = J^2 - 4*tau);
  my(g2 = a^2/12 - 2*J);
  my(g3 = -a^3/216 + a*J/6 - 1);
  my(Delta = g2^3 - 27*g3^2);
  [g2, g3, Delta];
};

ell_curve_from_J(J, tau) =
{
  my(w = weierstrass_invariants(J, tau));
  my(g2 = w[1], g3 = w[2]);
  ellinit([0,0,0,-g2/4,-g3/4]);
};

translation_point_on_curve(J, tau) =
{
  my(a = J^2 - 4*tau);
  [a/12, 1/2];
};

curve_point_from_qrt(x, y, J, tau) =
{
  my(X = x*y);
  my(Y = x - y);
  my(P = quartic_to_weierstrass(X, Y, J, tau));
  my(u = P[1], v = P[2]);
  [u, v/2];
};

check_quartic_weierstrass(J, tau) =
{
  my(g2g3 = weierstrass_invariants(J, tau));
  my(g2 = g2g3[1], g3 = g2g3[2]);
  my(E = ell_curve_from_J(J, tau));
  my(w = ellperiods(E));
  my(Delta = g2^3 - 27*g3^2);

  print("J = ", J, "; g2 = ", g2, "; g3 = ", g3, "; Delta = ", Delta);
  print("Periods = ", w);

  if (imag(w[2]/w[1]) <= 0,
    print("Warning: the period ratio is not in the upper half-plane.");
  );

  print("poldisc = ", poldisc(quartic_poly(J, tau, 'X), 'X));
  print("256*Delta = ", 256*Delta);

  abs(poldisc(quartic_poly(J, tau, 'X), 'X) - 256*Delta) < 1e-30;
};

\\ ---------------------------------------------------------------------------
\\ QRT dynamics and fixed translation point
\\ ---------------------------------------------------------------------------

qrt_invariant(x, y, tau) = x*y + 1/x + 1/y + tau/(x*y);

qrt_state_from_seed(lambda, m, r, eta) =
{
  my(x2 = lambda*r/m^2);
  my(x3 = m*eta/r^2);
  [x2, x3];
};

qrt_step_pair(x, y, tau) =
{
  my(z = y);
  my(w = (y + tau)/(x*y^2));
  [z, w];
};

fixed_translation_point(J, tau) =
{
  my(a = J^2 - 4*tau);
  my(P = [a/12, 1/2]);
  P;
};

verify_qrt_translation(lambda, m, r, eta, tau, nsteps = 6) =
{
  my(J = somos_J(lambda, m, r, eta, tau));
  my(E = ell_curve_from_J(J, tau));
  my(x = lambda*r/m^2, y = m*eta/r^2);
  my(P = fixed_translation_point(J, tau));
  my(zP = ellpointtoz(E, P));
  my(zQ = ellpointtoz(E, curve_point_from_qrt(x, y, J, tau)));

  for (n = 1, nsteps,
    my(cur = [x, y]);
    my(next = qrt_step_pair(x, y, tau));
    my(Qn = curve_point_from_qrt(x, y, J, tau));
    my(Qnp1 = curve_point_from_qrt(next[1], next[2], J, tau));
    my(zn = ellpointtoz(E, Qn));
    my(znp1 = ellpointtoz(E, Qnp1));
    my(check = (sqrt(ellwp(E, znp1) - ellwp(E, zn))));
    x = next[1];
    y = next[2];
    print("step ", n, ": invariant = ", qrt_invariant(cur[1], cur[2], tau),
          ", Q_{n+1}-Q_n = P ? ", abs(znp1 - zn - zP) < 1e-30);
  );
};

\\ ---------------------------------------------------------------------------
\\ Sigma normalization and recurrence checks
\\ ---------------------------------------------------------------------------

sigma_lattice_from_J(J, tau) =
{
  my(E = ell_curve_from_J(J, tau));
  ellperiods(E);
};

sigma_representation(lambda, m, r, eta, tau, z0, delta) =
{
  my(L = sigma_lattice_from_J(somos_J(lambda, m, r, eta, tau), tau));
  my(sigma_delta = ellsigma(L, delta));
  my(sigma_1 = ellsigma(L, z0 + delta));
  my(sigma_2 = ellsigma(L, z0 + 2*delta));

  my(B = m*sigma_1*sigma_delta^3 / (lambda*sigma_2));
  my(A = lambda^2*sigma_2 / (m*sigma_delta^2*sigma_1^2));
  [A, B, sigma_delta, sigma_1, sigma_2];
};

somos_sigma_value(lambda, m, r, eta, tau, z0, delta, n) =
{
  my(L = sigma_lattice_from_J(somos_J(lambda, m, r, eta, tau), tau));
  my(sigma_delta = ellsigma(L, delta));
  my(A, B, s1, s2);
  [A, B, s1, s2] = sigma_representation(lambda, m, r, eta, tau, z0, delta);
  A * B^n * ellsigma(L, z0 + n*delta) / sigma_delta^(n^2);
};

check_sigma_workflow_classical() =
{
  my(lambda = 1, m = 1, r = 1, eta = 1, tau = 1);
  my(J = somos_J(lambda, m, r, eta, tau));
  my(E = ell_curve_from_J(J, tau));
  my(L = ellperiods(E));
  my(x2 = lambda*r/m^2, x3 = m*eta/r^2);
  my(Q2 = curve_point_from_qrt(x2, x3, J, tau));
  my(next = qrt_step_pair(x2, x3, tau));
  my(Q3 = curve_point_from_qrt(next[1], next[2], J, tau));
  my(P = fixed_translation_point(J, tau));
  my(zP = ellpointtoz(E, P));
  my(z2 = ellpointtoz(E, Q2));
  my(z3 = ellpointtoz(E, Q3));
  my(delta = zP);
  my(z0 = z2 - 2*delta);

  my(A, B, sd, s1, s2);
  [A, B, sd, s1, s2] = sigma_representation(lambda, m, r, eta, tau, z0, delta);
  my(H = [0]);
  for (n = 1, 10,
    my(hn = A * B^n * ellsigma(L, z0 + n*delta) / sd^(n^2));
    listput(H, hn);
  );

  print("H1..H10 from sigma formula = ", Vec(H));
  print("Exact Somos values           = ", [1,1,1,1,2,3,7,23,47,123]);
  print("J = ", J, "; translation point = ", P);
  print("z0 = ", z0, "; delta = ", delta);

  [H, E, L, z0, delta, J];
};

\\ ---------------------------------------------------------------------------
\\ Executable demonstration driver
\\ ---------------------------------------------------------------------------

demo_sigma_workflow() =
{
  default(realprecision, 80);
  my(lambda = 1, m = 1, r = 1, eta = 1, tau = 1);
  my(J = somos_J(lambda, m, r, eta, tau));
  my(g2g3 = weierstrass_invariants(J, tau));
  my(E = ell_curve_from_J(J, tau));
  my(L = ellperiods(E));
  my(x2 = lambda*r/m^2, x3 = m*eta/r^2);
  my(Q2 = curve_point_from_qrt(x2, x3, J, tau));
  my(next = qrt_step_pair(x2, x3, tau));
  my(Q3 = curve_point_from_qrt(next[1], next[2], J, tau));
  my(P = fixed_translation_point(J, tau));
  my(zP = ellpointtoz(E, P));
  my(z2 = ellpointtoz(E, Q2));
  my(z3 = ellpointtoz(E, Q3));
  my(delta = zP);
  my(z0 = z2 - 2*delta);

  my(A, B, sd, s1, s2);
  [A, B, sd, s1, s2] = sigma_representation(lambda, m, r, eta, tau, z0, delta);

  my(H = vector(8, n,
    A * B^n * ellsigma(L, z0 + n*delta) / sd^(n^2)
  ));

  print("Generative data: lambda=", lambda, ", m=", m, ", r=", r,
        ", eta=", eta, ", tau=", tau);
  print("J = ", J);
  print("g2, g3, Delta = ", g2g3);
  print("z0 = ", z0);
  print("delta = ", delta);
  print("A = ", A, "; B = ", B);
  print("H_1..H_8 from sigma formula = ", H);
  print("Exact Somos values            = ", [1,1,1,1,2,3,7,23]);

  my(ok = 1);
  for (n = 1, 8,
    if (abs(H[n] - [1,1,1,1,2,3,7,23][n]) > 1e-30,
      ok = 0;
    );
  );
  if (ok,
    print("sigma check: PASS"),
    print("sigma check: FAIL")
  );

  [J, g2g3, E, L, z0, delta, A, B, H];
};
classical_example() =
{
  demo_sigma_workflow();
};
\\ End of script
