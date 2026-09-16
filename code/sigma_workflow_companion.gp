\\ PARI/GP companion for the algebraic-to-sigma workflow.

somos_J(lambda, m, r, eta, tau) =
{
  lambda*eta/(m*r)
  + m^2/(lambda*r)
  + r^2/(m*eta)
  + tau*m*r/(lambda*eta);
};

quartic_poly(J, tau, X) = (X^2 - J*X + tau)^2 - 4*X;

qrt_invariant(x, y, tau) = x*y + 1/x + 1/y + tau/(x*y);
qrt_step(x, y, tau) = [y, (y + tau)/(x*y^2)];
qrt_step_pair(x, y, tau) = qrt_step(x, y, tau);

somos_recurrence_step(v, tau) =
{
  my(n = #v);
  if (n < 4, error("Need at least four values to advance the Somos-4 orbit"));
  if (v[n-3] == 0, error("Zero denominator in Somos-4 recurrence"));
  (v[n]*v[n-2] + tau*v[n-1]^2) / v[n-3];
};

somos_orbit(lambda, m, r, eta, tau, N) =
{
  my(v = List([lambda, m, r, eta]));
  if (N < 1, return([]));
  for (n = 5, N,
    listput(v, somos_recurrence_step(v, tau));
  );
  Vec(v)[1..min(N, #v)];
};

quartic_to_weierstrass(X, Y, J, tau) =
{
  my(U = (Y + X^2 - J*X + tau)/2);
  my(V = U*(2*X - J) - 1);
  [U + (J^2 - 4*tau)/12, V];
};

weierstrass_to_quartic(u, v, J, tau) =
{
  my(U = u - (J^2 - 4*tau)/12);
  if (U == 0, error("Affine inverse map hits the excluded U = 0 chart"));
  my(X = (v + J*U + 1)/(2*U));
  [X, 2*U - X^2 + J*X - tau];
};

weierstrass_invariants(J, tau) =
{
  my(a = J^2 - 4*tau);
  my(g2 = a^2/12 - 2*J);
  my(g3 = -a^3/216 + a*J/6 - 1);
  [g2, g3, g2^3 - 27*g3^2];
};

ell_curve_from_J(J, tau) =
{
  my(w = weierstrass_invariants(J, tau));
  ellinit([0, 0, 0, -w[1]/4, -w[2]/4]);
};

fixed_translation_point(J, tau) =
{
  my(a = J^2 - 4*tau);
  [a/12, 1/2];       \\ PARI coordinates [u,v/2]
};

translation_point_on_curve(J, tau) = fixed_translation_point(J, tau);

curve_point_from_qrt(x, y, J, tau) =
{
  my(P = quartic_to_weierstrass(x*y, x-y, J, tau));
  [P[1], P[2]/2];    \\ PARI coordinates [u,v/2]
};

check_discriminant(J, tau) =
{
  my(w = weierstrass_invariants(J, tau));
  my(F = quartic_poly(J, tau, 'X));
  [poldisc(F, 'X), 256*w[3], poldisc(F, 'X) - 256*w[3]];
};

check_quartic_weierstrass(J, tau) =
{
  my(w = weierstrass_invariants(J, tau));
  my(E = ell_curve_from_J(J, tau));
  my(W = ellperiods(E));
  my(omega1 = W[1]/2, omega2 = -W[2]/2);
  my(tau_mod = omega2/omega1);

  print("J = ", J, "; g2 = ", w[1], "; g3 = ", w[2], "; Delta = ", w[3]);
  print("PARI full periods W = ", W);
  print("Reference half-periods: omega1 = ", omega1, ", omega2 = ", omega2);
  print("tau_mod = ", tau_mod);
  print("discriminant check = ", check_discriminant(J, tau));

  if (imag(tau_mod) <= 0,
    print("Warning: tau_mod is not in the upper half-plane.");
  );

  abs(check_discriminant(J, tau)[3]) < 1e-30;
};

verify_qrt_translation(lambda, m, r, eta, tau, nsteps = 6) =
{
  my(J = somos_J(lambda, m, r, eta, tau));
  my(E = ell_curve_from_J(J, tau));
  my(x = lambda*r/m^2, y = m*eta/r^2);
  my(P = fixed_translation_point(J, tau));
  for (k = 1, nsteps,
    my(Qn = curve_point_from_qrt(x, y, J, tau));
    my(next = qrt_step(x, y, tau));
    my(Qnp1 = curve_point_from_qrt(next[1], next[2], J, tau));
    print("step ", k,
          ": invariant error = ", qrt_invariant(x, y, tau) - J,
          ", translation exact = ", ellsub(E, Qnp1, Qn) == P);
    x = next[1];
    y = next[2];
  );
};

sigma_lattice_from_J(J, tau) =
{
  my(E = ell_curve_from_J(J, tau));
  ellperiods(E);
};

sigma_representation(lambda, m, r, eta, tau, z0, delta) =
{
  my(L = sigma_lattice_from_J(somos_J(lambda, m, r, eta, tau), tau));
  my(sd = ellsigma(L, delta));
  my(S1 = ellsigma(L, z0 + delta));
  my(S2 = ellsigma(L, z0 + 2*delta));
  my(B = m*S1*sd^3 / (lambda*S2));
  my(A = lambda^2*S2 / (m*sd^2*S1^2));
  [A, B, sd, S1, S2];
};

sigma_parameters(lambda, m, r, eta, tau) =
{
  my(J = somos_J(lambda, m, r, eta, tau));
  my(E = ell_curve_from_J(J, tau));
  my(x2 = lambda*r/m^2, x3 = m*eta/r^2);
  my(Q2 = curve_point_from_qrt(x2, x3, J, tau));
  my(P = fixed_translation_point(J, tau));
  my(L = ellperiods(E));
  my(delta = ellpointtoz(E, P));
  my(z2 = ellpointtoz(E, Q2));
  \\ In the H_1-started normalization, Q_n corresponds to z0 + (n+1)*delta.
  my(z0 = z2 - 3*delta);
  my(sd = ellsigma(L, delta));
  my(S1 = ellsigma(L, z0 + delta)/sd);
  my(S2 = ellsigma(L, z0 + 2*delta)/sd^4);
  my(B = m*S1/(lambda*S2));
  my(A = lambda^2*S2/(m*S1^2));
  [E, L, z0, delta, A, B];
};

sigma_value(sigpar, n) =
{
  my(L = sigpar[2], z0 = sigpar[3], delta = sigpar[4]);
  my(A = sigpar[5], B = sigpar[6]);
  A*B^n*ellsigma(L, z0 + n*delta)/ellsigma(L, delta)^(n^2);
};

somos_sigma_value(lambda, m, r, eta, tau, z0, delta, n) =
{
  my(L = sigma_lattice_from_J(somos_J(lambda, m, r, eta, tau), tau));
  my(A, B, sd, S1, S2);
  [A, B, sd, S1, S2] = sigma_representation(lambda, m, r, eta, tau, z0, delta);
  A*B^n*ellsigma(L, z0 + n*delta)/sd^(n^2);
};

workflow_demo(lambda, m, r, eta, tau, N = 10, prec = 80) =
{
  default(realprecision, prec);
  my(J = somos_J(lambda, m, r, eta, tau));
  my(w = weierstrass_invariants(J, tau));
  if (w[3] == 0, error("Singular quartic / elliptic curve"));
  my(sigpar = sigma_parameters(lambda, m, r, eta, tau));
  my(exact = somos_orbit(lambda, m, r, eta, tau, N));
  my(approx = vector(N, n, sigma_value(sigpar, n)));
  my(err = vector(N, n, abs(approx[n] - exact[n])));
  print("J = ", J);
  print("[g2,g3,Delta] = ", w);
  print("ellperiods(E) = ", ellperiods(sigpar[1]));
  print("z0 = ", sigpar[3], "; delta = ", sigpar[4]);
  print("A = ", sigpar[5], "; B = ", sigpar[6]);
  print("exact orbit = ", exact);
  print("sigma orbit = ", approx);
  print("absolute errors = ", err);
  [J, w, ellperiods(sigpar[1]), sigpar, exact, approx, err];
};

demo_sigma_workflow() =
{
  workflow_demo(1, 1, 1, 1, 1, 8, 80);
};

check_sigma_workflow_classical() =
{
  workflow_demo(1, 1, 1, 1, 1, 10, 80);
};

classical_example() =
{
  workflow_demo(1, 1, 1, 1, 1, 10, 80);
};

nonunit_example() =
{
  workflow_demo(2, 1, 1, 3, 2, 10, 80);
};
