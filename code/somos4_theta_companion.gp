\\ PARI/GP companion for the draft chain
\\   - drafts/direct_somos4_algebraic_gf.tex
\\   - drafts/six_parameter_somos4_followup.tex
\\   - drafts/theta_kernel_formula.tex
\\
\\ Scope of this script:
\\   1. implement the five-parameter algebraic generating function exactly
\\      as stated in the direct generating-function paper;
\\   2. implement the six-parameter transport and parity orientation from
\\      the follow-up paper;
\\   3. recover (lambda,m,r,eta,alpha,tau) from signed Hankel data; and
\\   4. instantiate explicit elliptic sigma data for the direct-paper slice
\\      and verify the kernel coefficient identity from theta_kernel_formula.
\\
\\ Symbol map used here.
\\   direct paper:     (lambda, m, r, eta, tau)
\\   six-param paper:  (lambda, m, r, eta, alpha, tau), q6^6 = alpha
\\   theta paper:      kernel scaling nome q_star
\\   specialization:   the direct paper is the alpha = 1 slice of the
\\                     six-parameter family.
\\
\\ Important notation separation.
\\   q6     sixth root used in the six-parameter transport, q6^6 = alpha
\\   q_star nome-aligned kernel scaling parameter from theta_kernel_formula
\\
\\ The follow-up paper resolves the sign ambiguity at the companion level:
\\ parity conjugation F(x) -> F(-x) preserves ordinary Hankel determinants
\\ and multiplies the once-shifted determinant of order N by (-1)^N.
\\ This script encodes that orientation explicitly.

somos4_abs(x) = if (type(x) == "t_COMPLEX", abs(x), abs(x));

somos4_print_status(tag, msg) =
{
  print("[", tag, "] ", msg);
};

somos4_print_header() =
{
  print("============================================================");
  print("Somos-4 theta companion (five- and six-parameter papers)");
  print("PARI/GP version: ", version());
  print("realprecision = ", default(realprecision));
  print("direct-paper specialization: alpha = 1, beta = tau");
  print("six-parameter transport root: q6^6 = alpha");
  print("theta-paper nome parameter remains q_star and is distinct from q6");
  print("============================================================");
};

somos4_symbol_map() =
{
  print("Symbol / convention map");
  print("  H_n               ordinary Hankel determinants");
  print("  (lambda,m,r,eta)  H_1, H_2, H_3, H_4 in the direct paper");
  print("  (alpha,tau)       six-parameter Somos-4 coefficients");
  print("  q6                transport root with q6^6 = alpha");
  print("  tau               second Somos coefficient in the direct and follow-up papers");
  print("  (alpha,beta)      theta-paper general coefficients; direct-paper slice has alpha=1, beta=tau");
  print("  G(x)              ordinary moment generating function");
  print("  A_S,B_S,z0,kappa  sigma orbit data named in the theta paper only");
  print("  q_star            nome-aligned scaling parameter from the theta paper");
  print("  D_N               once-shifted determinant det(g_{i+j+1})");
  print("  orientation       parity choice F(x) or F(-x), seen only by shifted determinants");
};

somos4_J(lambda, m, r, eta, tau) =
{
  lambda*eta/(m*r)
  + m^2/(lambda*r)
  + r^2/(m*eta)
  + tau*m*r/(lambda*eta);
};

somos4_hankel_det(coeffs, n, shift = 0) =
{
  if (n < 0, error("hankel_det needs n >= 0"));
  if (n == 0, return(1));
  if (#coeffs < 2*n - 1 + shift,
    error("not enough coefficients for requested Hankel determinant")
  );
  matdet(matrix(n, n, i, j, coeffs[i + j - 1 + shift]));
};

somos4_hankel_prefix(coeffs, max_n, shift = 0) =
{
  vector(max_n + 1, n, somos4_hankel_det(coeffs, n - 1, shift));
};

somos4_recurrence_step(h, tau) =
{
  my(n = #h);
  if (n < 4, error("need at least four Hankel values"));
  if (h[n-3] == 0, error("zero denominator in Somos-4 recurrence"));
  (h[n]*h[n-2] + tau*h[n-1]^2) / h[n-3];
};

somos4_orbit(lambda, m, r, eta, tau, N) =
{
  my(v = List([lambda, m, r, eta]));
  if (N <= 0, return([]));
  if (N <= 4, return(Vec(v)[1..N]));
  for (k = 5, N,
    listput(v, somos4_recurrence_step(Vec(v), tau));
  );
  Vec(v);
};

somos4_Apoly(lambda, eta, m, r, tau, z) =
{
  lambda*eta*m*r^2*(tau - eta)*z^3
  + r*(-(lambda^2*eta*m + m^2*(m + r^2))*tau
       + (2*m - 1)*lambda^2*eta^2 + eta*m^2*(m + r^2) - lambda*r*(m + r^2))*z^2
  + lambda*(m^2*r^2*tau - (m - 1)*lambda^2*eta^2
       - m*(m^2 + 2*m*r^2 - m - r^2)*eta + lambda*r^3)*z
  + lambda^2*eta*m*(m - 1)*r;
};

somos4_Bpoly(lambda, eta, m, r, tau, z) =
{
  (-lambda^2*eta*m*r^2*tau)*z^3
  + r*((2*lambda^3*eta*m + lambda*m^2*(2*m + r^2))*tau
       - (2*m - 1)*lambda^3*eta^2 - lambda*eta*m^3 + lambda^2*r*(2*m + r^2))*z^2
  + lambda^2*(-2*m^2*r^2*tau + 2*(m - 1)*lambda^2*eta^2
       + m*(2*m^2 + 2*m*r^2 - 2*m - r^2)*eta - 2*lambda*r^3)*z
  - 2*lambda^3*eta*m*(m - 1)*r;
};

somos4_Cpoly(lambda, eta, m, r, tau, z) =
{
  -lambda^2*m*r*(tau*(lambda^2*eta + m^2) + lambda*r)*z^2
  + (lambda^3*m^2*r^2*tau + lambda^4*r^3
     - lambda^3*eta*(m - 1)*(lambda^2*eta + m^2))*z
  + lambda^4*eta*m*(m - 1)*r;
};

somos4_select_branch(lambda, eta, m, r, tau, nterms) =
{
  my(z = 'z + O('z^nterms));
  my(A = somos4_Apoly(lambda, eta, m, r, tau, z));
  my(B = somos4_Bpoly(lambda, eta, m, r, tau, z));
  my(C = somos4_Cpoly(lambda, eta, m, r, tau, z));
  my(D = B^2 - 4*A*C);
  my(S = sqrt(D));
  my(root_minus, root_plus, hminus, hplus);

  if (valuation(D, 'z) % 2,
    error("discriminant has odd valuation; no formal square root branch in this chart")
  );

  if (polcoeff(A, 0) == 0,
    root_minus = -2*C / (B - S);
    root_plus = -2*C / (B + S),
    root_minus = (-B - S) / (2*A);
    root_plus = (-B + S) / (2*A)
  );

  hminus = somos4_hankel_prefix(Vec(root_minus), 4)[2..5];
  hplus = somos4_hankel_prefix(Vec(root_plus), 4)[2..5];

  if (hminus == [lambda, m, r, eta], return(root_minus));
  if (hplus == [lambda, m, r, eta], return(root_plus));
  error("could not identify the required algebraic branch from the first four Hankel determinants");
};

somos4_coeff_vector(lambda, eta, m, r, tau, nterms) =
{
  Vec(somos4_select_branch(lambda, eta, m, r, tau, nterms));
};

somos4_scaled_coeffs(coeffs, q) =
{
  vector(#coeffs, k, coeffs[k] * q^(k - 1));
};

somos4_orient_coeffs(coeffs, orient) =
{
  if (!(orient == 1 || orient == -1),
    error("orientation must be +1 or -1")
  );
  vector(#coeffs, k, coeffs[k] * orient^(k - 1));
};

somos4_shifted_hankel_prefix(coeffs, max_n) =
{
  vector(max_n + 1, n, somos4_hankel_det(coeffs, n - 1, 1));
};

somos4_scale_six_params(lambda, m, r, eta, alpha, tau, q6) =
{
  if (q6^6 != alpha,
    error("q6 must satisfy q6^6 = alpha exactly")
  );
  [lambda, m/q6^2, r/q6^6, eta/q6^12, tau/q6^8];
};

somos4_six_coeff_vector(lambda, m, r, eta, alpha, tau, q6, orient, nterms) =
{
  my(base = somos4_scale_six_params(lambda, m, r, eta, alpha, tau, q6));
  my(coeffs = somos4_coeff_vector(base[1], base[4], base[2], base[3], base[5], nterms));
  coeffs = somos4_scaled_coeffs(coeffs, q6);
  somos4_orient_coeffs(coeffs, orient);
};

somos4_recover_six_parameters(h) =
{
  if (#h < 6,
    error("need at least H_1 through H_6 for six-parameter recovery")
  );
  my(lambda = h[1], m = h[2], r = h[3], eta = h[4], h5 = h[5], h6 = h[6]);
  my(det = eta^3*m - h5*r^3);
  if (det == 0,
    error("recovery system for (alpha,tau) is singular")
  );
  my(alpha = (h5*lambda*eta^2 - r^2*h6*m) / det);
  my(tau = (eta*m*h6*m - h5*lambda*h5*r) / det);
  [lambda, m, r, eta, alpha, tau];
};

somos4_check_six_parameter_recovery(h, lambda, m, r, eta, alpha, tau) =
{
  my(recovered = somos4_recover_six_parameters(h));
  if (recovered != [lambda, m, r, eta, alpha, tau],
    error("six-parameter recovery from signed Hankel data failed")
  );
  recovered;
};

somos4_check_shifted_companion_exact(coeffs, q6, orient, upto_n) =
{
  for (n = 1, upto_n,
    my(lhs = somos4_hankel_det(coeffs, n, 1));
    my(rhs = orient^n * q6^(-3*n - 2) * somos4_hankel_det(coeffs, n + 2));
    if (lhs != rhs,
      error(Str("shifted graded companion law failed at N=", n))
    );
  );
  1;
};

somos4_check_six_recurrence_exact(coeffs, alpha, tau, upto_n) =
{
  my(h = somos4_hankel_prefix(coeffs, upto_n));
  for (n = 1, upto_n - 4,
    if (h[n+5] * h[n+1] != alpha * h[n+4] * h[n+2] + tau * h[n+3]^2,
      error(Str("six-parameter Somos-4 recurrence failed at n=", n))
    );
  );
  h;
};

somos4_six_recurrence_step(v, alpha, tau) =
{
  my(n = #v);
  if (n < 4, error("need at least four values to advance the six-parameter Somos-4 orbit"));
  if (v[n-3] == 0, error("zero denominator in six-parameter Somos-4 recurrence"));
  (alpha*v[n]*v[n-2] + tau*v[n-1]^2) / v[n-3];
};

somos4_six_orbit(lambda, m, r, eta, alpha, tau, N) =
{
  my(v = List([lambda, m, r, eta]));
  if (N <= 0, return([]));
  if (N <= 4, return(Vec(v)[1..N]));
  for (k = 5, N,
    listput(v, somos4_six_recurrence_step(Vec(v), alpha, tau));
  );
  Vec(v);
};

somos4_check_six_initial_hankels(coeffs, lambda, m, r, eta) =
{
  my(h = somos4_hankel_prefix(coeffs, 4)[2..5]);
  if (h != [lambda, m, r, eta],
    error("transported initial Hankel determinants do not match (lambda,m,r,eta)")
  );
  h;
};

somos4_check_six_low_order_values(coeffs, lambda, m, r, eta, alpha, tau) =
{
  my(h = somos4_hankel_prefix(coeffs, 6)[2..7]);
  my(h5 = (alpha*eta*m + tau*r^2) / lambda);
  my(h6 = (alpha*h5*r + tau*eta^2) / m);
  if (h[5] != h5 || h[6] != h6,
    error("low-order six-parameter recurrence values do not match transported orbit")
  );
  h;
};

somos4_weierstrass_invariants(J, tau) =
{
  my(a = J^2 - 4*tau);
  my(g2 = a^2/12 - 2*J);
  my(g3 = -a^3/216 + a*J/6 - 1);
  [g2, g3, g2^3 - 27*g3^2];
};

somos4_ell_curve_from_J(J, tau) =
{
  my(w = somos4_weierstrass_invariants(J, tau));
  ellinit([0, 0, 0, -w[1]/4, -w[2]/4]);
};

somos4_fixed_translation_point(J, tau) =
{
  my(a = J^2 - 4*tau);
  [a/12, 1/2];
};

somos4_quartic_to_weierstrass(X, Y, J, tau) =
{
  my(U = (Y + X^2 - J*X + tau)/2);
  my(V = U*(2*X - J) - 1);
  [U + (J^2 - 4*tau)/12, V];
};

somos4_curve_point_from_qrt(x, y, J, tau) =
{
  my(P = somos4_quartic_to_weierstrass(x*y, x-y, J, tau));
  [P[1], P[2]/2];
};

somos4_sigma_parameters(lambda, m, r, eta, tau) =
{
  my(J = somos4_J(lambda, m, r, eta, tau));
  my(E = somos4_ell_curve_from_J(J, tau));
  my(x2 = lambda*r/m^2, x3 = m*eta/r^2);
  my(Q2 = somos4_curve_point_from_qrt(x2, x3, J, tau));
  my(P = somos4_fixed_translation_point(J, tau));
  my(L = ellperiods(E));
  my(kappa = ellpointtoz(E, P));
  my(z2 = ellpointtoz(E, Q2));
  my(z0 = z2 - 3*kappa);
  my(sd = ellsigma(L, kappa));
  my(S1 = ellsigma(L, z0 + kappa)/sd);
  my(S2 = ellsigma(L, z0 + 2*kappa)/sd^4);
  my(B = m*S1/(lambda*S2));
  my(A = lambda^2*S2/(m*S1^2));
  [E, L, z0, kappa, A, B, P, Q2];
};

somos4_sigma_value(sigpar, n) =
{
  my(L = sigpar[2], z0 = sigpar[3], kappa = sigpar[4]);
  my(A = sigpar[5], B = sigpar[6]);
  A*B^n*ellsigma(L, z0 + n*kappa)/ellsigma(L, kappa)^(n^2);
};

somos4_sigma_orbit(sigpar, N) =
{
  vector(N, n, somos4_sigma_value(sigpar, n));
};

somos4_near_rational(x, tol) =
{
  if (somos4_abs(imag(x)) > tol,
    error("expected nearly real sigma value before rational reconstruction")
  );
  bestappr(real(x));
};

somos4_recover_signed_hankels_from_sigma(sigpar, N, tol) =
{
  my(vals = somos4_sigma_orbit(sigpar, N));
  vector(N, n, somos4_near_rational(vals[n], tol));
};

somos4_theta_qstar(sigpar) =
{
  my(L = sigpar[2], kappa = sigpar[4]);
  my(omega1 = L[1]/2, omega3 = -L[2]/2);
  my(tau_mod = omega3/omega1);
  my(eta1 = ellzeta(L, omega1));
  my(a = eta1/(2*omega1));
  ellsigma(L, kappa) * exp(Pi*I*tau_mod/2) * exp(-a*kappa^2);
};

somos4_transport_sigma_gauge(sigpar, q6) =
{
  my(A = sigpar[5], B = sigpar[6]);
  [sigpar[1], sigpar[2], sigpar[3], sigpar[4], A, B/q6, sigpar[7], sigpar[8], q6];
};

somos4_transport_sigma_value(tsigpar, n) =
{
  my(base = [tsigpar[1], tsigpar[2], tsigpar[3], tsigpar[4], tsigpar[5], tsigpar[6] * tsigpar[9], tsigpar[7], tsigpar[8]]);
  tsigpar[9]^(n*(n-1)) * somos4_sigma_value(base, n);
};

somos4_transport_sigma_orbit(tsigpar, N) =
{
  vector(N, n, somos4_transport_sigma_value(tsigpar, n));
};

somos4_transport_theta_qstar(tsigpar) =
{
  somos4_theta_qstar([tsigpar[1], tsigpar[2], tsigpar[3], tsigpar[4], tsigpar[5], tsigpar[6] * tsigpar[9], tsigpar[7], tsigpar[8]]) / tsigpar[9];
};

somos4_theta2_const(p, nmax) =
{
  my(s = 0);
  for (n = -nmax, nmax,
    s += p^(2*(n + 1/2)^2);
  );
  s;
};

somos4_theta3_const(p, nmax) =
{
  my(s = 0);
  for (n = -nmax, nmax,
    s += p^(2*n^2);
  );
  s;
};

somos4_theta1prime0(p, nmax) =
{
  my(s = 0);
  for (n = 0, nmax,
    s += 2 * (-1)^n * (2*n + 1) * p^((n + 1/2)^2);
  );
  s;
};

somos4_Dp_theta2_const(p, nmax) =
{
  my(s = 0);
  for (n = -nmax, nmax,
    s += 2*(n + 1/2)^2 * p^(2*(n + 1/2)^2);
  );
  s;
};

somos4_Dp_theta3_const(p, nmax) =
{
  my(s = 0);
  for (n = -nmax, nmax,
    s += 2*n^2 * p^(2*n^2);
  );
  s;
};

somos4_theta_aell(ell, p, T0, T1) =
{
  if (ell % 2 == 0,
    p^(ell^2/2) * T0,
    -p^(ell^2/2) * T1
  );
};

somos4_theta_Delta(p, nmax) =
{
  my(T0 = somos4_theta2_const(p, nmax), T1 = somos4_theta3_const(p, nmax));
  my(D0 = somos4_Dp_theta2_const(p, nmax), D1 = somos4_Dp_theta3_const(p, nmax));
  D0/T0 - D1/T1;
};

somos4_theta_aell_direct(sigpar, ell, nmax) =
{
  my(L = sigpar[2], omega1 = L[1]/2, omega3 = -L[2]/2);
  my(tau_mod = omega3/omega1, p = exp(Pi*I*tau_mod));
  my(s = 0);
  for (n = -nmax, nmax,
    s += (-1)^ell * p^((n + 1/2)^2 + (ell - n - 1/2)^2);
  );
  s;
};

somos4_theta_bell_convolution(sigpar, ell, nmax) =
{
  my(L = sigpar[2], omega1 = L[1]/2, omega3 = -L[2]/2);
  my(tau_mod = omega3/omega1, p = exp(Pi*I*tau_mod));
  my(lambda = Pi/(2*omega1));
  my(eta1 = ellzeta(L, omega1));
  my(a = eta1/(2*omega1));
  my(s = 0);
  for (n = -nmax, nmax,
    s += (2*n + 1 - ell)^2 * p^((n + 1/2)^2 + (ell - n - 1/2)^2);
  );
  2 * lambda^2 * (-1)^ell * s - 2 * a * somos4_theta_aell_direct(sigpar, ell, nmax);
};

somos4_theta_antisymmetric_coeff(sigpar, ell, m, nmax) =
{
  my(aell = somos4_theta_aell_direct(sigpar, ell, nmax));
  my(am = somos4_theta_aell_direct(sigpar, m, nmax));
  my(bell = somos4_theta_bell_convolution(sigpar, ell, nmax));
  my(bm = somos4_theta_bell_convolution(sigpar, m, nmax));
  aell*bm - bell*am;
};

somos4_theta_parity_sum(eps, Y, p, nmax) =
{
  my(s = 0);
  for (n = -nmax, nmax,
    if ((n % 2 + 2) % 2 == eps,
      s += p^(n^2/4) * Y^n;
    );
  );
  s;
};

somos4_kernel_direct(sigpar, qstar, t, z, nmax) =
{
  my(S1 = 0, S2 = 0);
  for (n = -nmax, nmax,
    my(Hn = somos4_sigma_value(sigpar, n));
    my(Wn = Hn * qstar^(n*(n-1)));
    S1 += Wn * (t*z)^n;
    S2 += Wn * (t/z)^n;
  );
  S1 * S2;
};

somos4_kernel_theta_series(sigpar, qstar, t, z, lmmax, nmax) =
{
  my(L = sigpar[2], z0 = sigpar[3], kappa = sigpar[4]);
  my(A = sigpar[5], B = sigpar[6]);
  my(omega1 = L[1]/2, omega3 = -L[2]/2);
  my(tau_mod = omega3/omega1, p = exp(Pi*I*tau_mod));
  my(eta1 = ellzeta(L, omega1));
  my(a = eta1/(2*omega1));
  my(Csigma = 2*omega1/(Pi*somos4_theta1prime0(p, nmax)));
  my(lambda = Pi/(2*omega1), gamma = lambda*kappa/2, x0 = lambda*z0);
  my(Xstar = B*t/qstar * exp(2*a*z0*kappa));
  my(total = 0);
  for (eps = 0, 1,
    for (ell = -lmmax, lmmax,
      my(Th1 = somos4_theta_parity_sum(eps, Xstar * exp(2*I*ell*gamma), p, nmax));
      for (m = -lmmax, lmmax,
        my(Th2 = somos4_theta_parity_sum(eps, z * exp(2*I*m*gamma), p, nmax));
        total += exp(2*I*ell*x0)
          * somos4_theta_antisymmetric_coeff(sigpar, ell, m, nmax)
          * Th1 * Th2;
      );
    );
  );
  A^2 * Csigma^4 * exp(2*a*z0^2) * total;
};

somos4_kernel_direct_coeff(sigpar, qstar, t, k, nmax) =
{
  my(s = 0);
  for (n = -nmax, nmax,
    my(Wn = somos4_sigma_value(sigpar, n) * qstar^(n*(n-1)));
    my(Wnk = somos4_sigma_value(sigpar, n + k) * qstar^((n + k)*(n + k - 1)));
    s += Wnk * Wn * t^(2*n + k);
  );
  s;
};

somos4_kernel_preconvolution_coeff(sigpar, qstar, t, k, lmmax, nmax) =
{
  my(L = sigpar[2], z0 = sigpar[3], kappa = sigpar[4]);
  my(A = sigpar[5], B = sigpar[6]);
  my(omega1 = L[1]/2, omega3 = -L[2]/2);
  my(tau_mod = omega3/omega1, p = exp(Pi*I*tau_mod));
  my(eta1 = ellzeta(L, omega1));
  my(a = eta1/(2*omega1));
  my(Csigma = 2*omega1/(Pi*somos4_theta1prime0(p, nmax)));
  my(lambda = Pi/(2*omega1));
  my(gamma = lambda*kappa/2, x0 = lambda*z0);
  my(Xstar = B*t/qstar * exp(2*a*z0*kappa));
  my(eps = (k % 2 + 2) % 2, total = 0);
  for (ell = -lmmax, lmmax,
    my(Th1 = somos4_theta_parity_sum(eps, Xstar * exp(2*I*ell*gamma), p, nmax));
    for (m = -lmmax, lmmax,
      total += exp(2*I*ell*x0) * somos4_theta_antisymmetric_coeff(sigpar, ell, m, nmax)
        * Th1 * p^(k^2/4) * exp(2*I*m*gamma*k);
    );
  );
  A^2 * Csigma^4 * exp(2*a*z0^2) * total;
};

somos4_kernel_theta_coeff(sigpar, qstar, t, k, lmmax, nmax) =
{
  somos4_kernel_preconvolution_coeff(sigpar, qstar, t, k, lmmax, nmax);
};

somos4_probe_theta_coefficients(sigpar, qstar, t, max_k, lmmax, nmax) =
{
  vector(max_k + 1, k,
    my(cd = somos4_kernel_direct_coeff(sigpar, qstar, t, k - 1, nmax));
    my(ct = somos4_kernel_theta_coeff(sigpar, qstar, t, k - 1, lmmax, nmax));
    [k - 1, cd, ct, somos4_abs(cd - ct)]
  );
};

somos4_probe_preconvolution_coefficients(sigpar, qstar, t, max_k, lmmax, nmax) =
{
  vector(max_k + 1, k,
    my(cd = somos4_kernel_direct_coeff(sigpar, qstar, t, k - 1, nmax));
    my(cp = somos4_kernel_preconvolution_coeff(sigpar, qstar, t, k - 1, lmmax, nmax));
    [k - 1, cd, cp, somos4_abs(cd - cp), somos4_abs(cd + cp/2)]
  );
};

somos4_probe_theta_series_expansion(sigpar, qstar, t, z, lmmax, nmax) =
{
  my(kdir = somos4_kernel_direct(sigpar, qstar, t, z, nmax));
  my(ktheta = somos4_kernel_theta_series(sigpar, qstar, t, z, lmmax, nmax));
  [kdir, ktheta, somos4_abs(kdir - ktheta)];
};

somos4_check_theta_series_layer(sigpar, qstar, t, z, max_k, lmmax, nmax, tol) =
{
  my(coeffprobe = somos4_probe_theta_coefficients(sigpar, qstar, t, max_k, lmmax, nmax));
  my(seriesprobe = somos4_probe_theta_series_expansion(sigpar, qstar, t, z, lmmax, nmax));
  for (j = 1, #coeffprobe,
    if (coeffprobe[j][4] > tol,
      error(Str("theta-series coefficient reconstruction failed at k=", coeffprobe[j][1]))
    );
  );
  if (seriesprobe[3] > tol,
    error("full theta-series kernel reconstruction failed")
  );
  [coeffprobe, seriesprobe];
};

somos4_check_kernel_relation_from_orbit(h, alpha, beta, qstar, upto_n) =
{
  my(W = vector(#h, n, h[n] * qstar^(n*(n-1))));
  for (n = 1, upto_n,
    my(lhs = W[n+4] * W[n]);
    my(rhs = alpha*qstar^6*W[n+3]*W[n+1] + beta*qstar^8*W[n+2]^2);
    if (somos4_abs(lhs - rhs) > 1e-60,
      error(Str("theta-kernel coefficient relation failed at n=", n))
    );
  );
  1;
};

somos4_check_sigma_direct_workflow(lambda, m, r, eta, tau, N, nterms, prec, tol) =
{
  my(oldprec = default(realprecision));
  my(J, w, sigpar, exact, sigma_vals, recovered_h, recovered_params, coeffs, gf_h, qstar, err, theta_checks, theta_tol = 1e-24);
  default(realprecision, prec);
  J = somos4_J(lambda, m, r, eta, tau);
  w = somos4_weierstrass_invariants(J, tau);
  if (w[3] == 0,
    error("sigma direct workflow hit a singular elliptic curve")
  );
  sigpar = somos4_sigma_parameters(lambda, m, r, eta, tau);
  exact = somos4_orbit(lambda, m, r, eta, tau, N);
  sigma_vals = somos4_sigma_orbit(sigpar, N);
  err = vector(N, n, somos4_abs(sigma_vals[n] - exact[n]));
  for (n = 1, N,
    if (err[n] > tol,
      error(Str("sigma orbit mismatch at n=", n))
    );
  );
  recovered_h = somos4_recover_signed_hankels_from_sigma(sigpar, N, tol);
  recovered_params = somos4_recover_six_parameters(recovered_h[1..6]);
  if (recovered_params != [lambda, m, r, eta, 1, tau],
    error("parameter recovery from sigma-signed Hankel data failed")
  );
  coeffs = somos4_coeff_vector(recovered_params[1], recovered_params[4], recovered_params[2], recovered_params[3], recovered_params[6], nterms);
  gf_h = somos4_hankel_prefix(coeffs, N)[2..(N+1)];
  if (gf_h != recovered_h,
    error("generating-function Hankel data does not match sigma-recovered signed orbit")
  );
  qstar = somos4_theta_qstar(sigpar);
  somos4_check_kernel_relation_from_orbit(exact, 1, tau, qstar, N - 4);
  theta_checks = somos4_check_theta_series_layer(sigpar, qstar, 1/10, 6/5, 5, 10, nterms, theta_tol);
  print("------------------------------------------------------------");
  print("Elliptic sigma workflow tuple: ", [lambda, m, r, eta, tau]);
  print("J invariant / [g2,g3,Delta]: ", [J, w]);
  print("translation point P and orbit point Q2: ", [sigpar[7], sigpar[8]]);
  print("z0 and kappa: ", [sigpar[3], sigpar[4]]);
  print("A_S and B_S: ", [sigpar[5], sigpar[6]]);
  print("q_star from theta normalization: ", qstar);
  somos4_print_status("NUMERIC PASS", "sigma orbit matches the exact Somos-4 orbit to working precision");
  somos4_print_status("EXACT PASS", "first six signed Hankel values recovered from sigma data reconstruct (lambda,m,r,eta,alpha=1,tau)");
  somos4_print_status("EXACT PASS", "five-parameter generating function reconstructed from recovered data reproduces the same Hankel orbit");
  somos4_print_status("NUMERIC PASS", "theta-kernel coefficient identity verified from the sigma orbit and q_star");
  somos4_print_status("NUMERIC PASS", Str("theta-series coefficient reconstruction matches the direct kernel coefficients at t=1/10 through k=", 5));
  somos4_print_status("NUMERIC PASS", "full convolution-free theta double-series reconstruction matches the direct kernel at t=1/10, z=6/5");
  default(realprecision, oldprec);
};

somos4_check_sigma_transport_workflow(lambda, m, r, eta, alpha, tau, q6, N, prec, tol) =
{
  my(oldprec = default(realprecision));
  my(basepars, tsigpar, exact, sigma_vals, err, recovered_h, recovered_params, qstar);
  default(realprecision, prec);
  basepars = somos4_scale_six_params(lambda, m, r, eta, alpha, tau, q6);
  tsigpar = somos4_transport_sigma_gauge(somos4_sigma_parameters(basepars[1], basepars[2], basepars[3], basepars[4], basepars[5]), q6);
  exact = somos4_six_orbit(lambda, m, r, eta, alpha, tau, N);
  sigma_vals = somos4_transport_sigma_orbit(tsigpar, N);
  err = vector(N, n, somos4_abs(sigma_vals[n] - exact[n]));
  for (n = 1, N,
    if (err[n] > tol,
      error(Str("transported sigma orbit mismatch at n=", n))
    );
  );
  recovered_h = vector(N, n, somos4_near_rational(sigma_vals[n], tol));
  recovered_params = somos4_recover_six_parameters(recovered_h[1..6]);
  if (recovered_params != [lambda, m, r, eta, alpha, tau],
    error("transported sigma gauge did not recover the six parameters")
  );
  qstar = somos4_transport_theta_qstar(tsigpar);
  somos4_check_kernel_relation_from_orbit(exact, alpha, tau, qstar, N - 4);
  print("------------------------------------------------------------");
  print("Transported sigma-gauge workflow tuple: ", [lambda, m, r, eta, alpha, tau]);
  print("transport root q6 and q_star: ", [q6, qstar]);
  print("transported sigma gauge [A_S, B_S/q6]: ", [tsigpar[5], tsigpar[6]]);
  somos4_print_status("NUMERIC PASS", "transported sigma gauge reproduces the six-parameter orbit");
  somos4_print_status("EXACT PASS", "first six transported sigma Hankel values recover (lambda,m,r,eta,alpha,tau)");
  somos4_print_status("NUMERIC PASS", "transported q_star satisfies the theta-kernel coefficient identity for alpha != 1");
  default(realprecision, oldprec);
};

somos4_check_initial_hankels(lambda, m, r, eta, tau, nterms) =
{
  my(coeffs = somos4_coeff_vector(lambda, eta, m, r, tau, nterms));
  my(h = somos4_hankel_prefix(coeffs, 4)[2..5]);
  if (h != [lambda, m, r, eta],
    error("initial Hankel determinants do not match the direct-paper parameters")
  );
  [coeffs, h];
};

somos4_check_recurrence_exact(lambda, m, r, eta, tau, nterms, upto_n) =
{
  my(coeffs = somos4_coeff_vector(lambda, eta, m, r, tau, nterms));
  my(h = somos4_hankel_prefix(coeffs, upto_n));
  for (n = 1, upto_n - 4,
    if (h[n+5] * h[n+1] != h[n+4] * h[n+2] + tau * h[n+3]^2,
      error(Str("Somos-4 recurrence failed at n=", n))
    );
  );
  h;
};

somos4_check_scaling_law(lambda, m, r, eta, tau, nterms, upto_n, q) =
{
  my(coeffs = somos4_coeff_vector(lambda, eta, m, r, tau, nterms));
  my(scaled = somos4_scaled_coeffs(coeffs, q));
  for (n = 0, upto_n,
    my(lhs = somos4_hankel_det(scaled, n));
    my(rhs = q^(n*(n-1)) * somos4_hankel_det(coeffs, n));
    if (lhs != rhs,
      error(Str("Hankel scaling law failed at n=", n))
    );
  );
  1;
};

somos4_check_defining_equation(lambda, m, r, eta, tau, nterms) =
{
  my(z = 'z + O('z^nterms));
  my(G = somos4_select_branch(lambda, eta, m, r, tau, nterms));
  my(A = somos4_Apoly(lambda, eta, m, r, tau, z));
  my(B = somos4_Bpoly(lambda, eta, m, r, tau, z));
  my(C = somos4_Cpoly(lambda, eta, m, r, tau, z));
  my(residual = A*G^2 + B*G + C);
  if (residual != O('z^nterms),
    error("algebraic defining equation residual is not zero to the requested order")
  );
  1;
};

somos4_run_direct_paper_checks(lambda, m, r, eta, tau, nterms, upto_n, q) =
{
  print("------------------------------------------------------------");
  print("Direct-paper exact test tuple: ", [lambda, m, r, eta, tau]);
  print("J invariant: ", somos4_J(lambda, m, r, eta, tau));
  somos4_check_initial_hankels(lambda, m, r, eta, tau, nterms);
  somos4_print_status("EXACT PASS", "initial Hankel determinants match (lambda,m,r,eta)");
  somos4_check_recurrence_exact(lambda, m, r, eta, tau, nterms, upto_n);
  somos4_print_status("EXACT PASS", Str("Somos-4 recurrence verified through Hankel index ", upto_n));
  somos4_check_defining_equation(lambda, m, r, eta, tau, nterms);
  print("[FORMAL SERIES PASS through z^", nterms - 1, "] algebraic defining equation");
  somos4_check_scaling_law(lambda, m, r, eta, tau, nterms, min(upto_n, 6), q);
  print("[EXACT PASS] Hankel scaling law under G(x) -> G(", q, "*x)");
};

somos4_run_six_parameter_checks(lambda, m, r, eta, alpha, tau, q6, orient, nterms, upto_n) =
{
  my(coeffs, h);
  print("------------------------------------------------------------");
  print("Six-parameter transported test tuple: ", [lambda, m, r, eta, alpha, tau]);
  print("Transport root / orientation: ", [q6, orient]);
  coeffs = somos4_six_coeff_vector(lambda, m, r, eta, alpha, tau, q6, orient, nterms);
  somos4_check_six_initial_hankels(coeffs, lambda, m, r, eta);
  somos4_print_status("EXACT PASS", "transport preserves H_1 through H_4");
  h = somos4_check_six_recurrence_exact(coeffs, alpha, tau, upto_n);
  somos4_print_status("EXACT PASS", Str("six-parameter Somos-4 recurrence verified through Hankel index ", upto_n));
  somos4_check_six_low_order_values(coeffs, lambda, m, r, eta, alpha, tau);
  somos4_print_status("EXACT PASS", "low-order transported formulas for H_5 and H_6");
  somos4_check_six_parameter_recovery(h[2..7], lambda, m, r, eta, alpha, tau);
  somos4_print_status("EXACT PASS", "signed Hankel start data recovers (lambda,m,r,eta,alpha,tau)");
  somos4_check_shifted_companion_exact(coeffs, q6, orient, 4);
  somos4_print_status("EXACT PASS", "shifted graded companion law with parity orientation");
};

somos4_reference_run() =
{
  my(nterms = 20, upto_n = 8, qscale = 2, prec = 120, tol = 1e-50);
  somos4_print_header();
  somos4_symbol_map();
  somos4_run_direct_paper_checks(1, 1, 1, 1, 1, nterms, upto_n, qscale);
  somos4_run_direct_paper_checks(2, 1, 1, 3, 2, nterms, upto_n, qscale);
  somos4_run_six_parameter_checks(1, 1, 1, 1, 64, 1, 2, 1, nterms, upto_n);
  somos4_run_six_parameter_checks(1, 1, 1, 1, 64, 1, 2, -1, nterms, upto_n);
  somos4_check_sigma_direct_workflow(1, 1, 1, 1, 1, upto_n, nterms, prec, tol);
  somos4_check_sigma_direct_workflow(2, 1, 1, 3, 2, upto_n, nterms, prec, tol);
  somos4_check_sigma_transport_workflow(1, 1, 1, 1, 64, 1, 2, upto_n, prec, tol);
  somos4_check_sigma_transport_workflow(2, 1, 1, 3, 64, 2, 2, upto_n, prec, tol);
  print("------------------------------------------------------------");
  print("Summary");
  print("[PASS] five-parameter generating-function branch selection");
  print("[PASS] six-parameter transported generating-function branch");
  print("[PASS] generating-function defining equation");
  print("[PASS] Hankel determinants from generated coefficients");
  print("[PASS] signed recovery of (lambda,m,r,eta,alpha,tau) from Hankel data");
  print("[PASS] shifted determinant parity-orientation law");
  print("[PASS] explicit elliptic curve and sigma-orbit instantiation for the direct-paper slice");
  print("[PASS] parameter recovery from sigma data and regeneration of the five-parameter generating function");
  print("[PASS] theta-kernel coefficient identity from the sigma orbit and q_star");
  print("[PASS] theta-series coefficient reconstruction from the corrected antisymmetric layer");
  print("[PASS] full convolution-free theta double-series reconstruction at the sampled test point");
  print("[PASS] transported sigma-gauge verification for six-parameter alpha != 1 examples");
  print("[PASS] Hankel scaling law");
  print("[DONE] direct-paper end-to-end elliptic / generating-function / kernel verification completed");
};