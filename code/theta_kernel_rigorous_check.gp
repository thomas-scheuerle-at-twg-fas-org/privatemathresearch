\\ Rigorous PARI/GP double-check for the corrected theta-kernel layer.
\\
\\ Run from the code directory:
\\   gp -q theta_kernel_rigorous_check.gp > ../theta_kernel_rigorous_report.txt

read("somos4_theta_companion.gp");

rig_abs(x) = if (type(x) == "t_VEC" || type(x) == "t_COL", vecmax(vector(#x, i, abs(x[i]))), abs(x));

rig_raw_F(sigpar, x, nmax) =
{
  my(L = sigpar[2], omega1 = L[1]/2, omega3 = -L[2]/2);
  my(p = exp(Pi*I*(omega3/omega1)), s = 0);
  for (n = -nmax, nmax,
    s += (-1)^n * p^((n + 1/2)^2) * exp(I*(2*n + 1)*x);
  );
  s;
};

rig_raw_F1(sigpar, x, nmax) =
{
  my(L = sigpar[2], omega1 = L[1]/2, omega3 = -L[2]/2);
  my(p = exp(Pi*I*(omega3/omega1)), s = 0);
  for (n = -nmax, nmax,
    s += I*(2*n + 1) * (-1)^n * p^((n + 1/2)^2) * exp(I*(2*n + 1)*x);
  );
  s;
};

rig_raw_F2(sigpar, x, nmax) =
{
  my(L = sigpar[2], omega1 = L[1]/2, omega3 = -L[2]/2);
  my(p = exp(Pi*I*(omega3/omega1)), s = 0);
  for (n = -nmax, nmax,
    s += -(2*n + 1)^2 * (-1)^n * p^((n + 1/2)^2) * exp(I*(2*n + 1)*x);
  );
  s;
};

rig_coeff_even(exprfun, sigpar, ell, nmax, nsamp) =
{
  my(s = 0);
  for (j = 0, nsamp - 1,
    my(x = 2*Pi*j/nsamp);
    s += exprfun(sigpar, x, nmax) * exp(-2*I*ell*x);
  );
  s / nsamp;
};

rig_expr_A(sigpar, x, nmax) = rig_raw_F(sigpar, x, nmax)^2;

rig_expr_B(sigpar, x, nmax) =
{
  my(L = sigpar[2], omega1 = L[1]/2);
  my(lambda = Pi/(2*omega1));
  my(eta1 = ellzeta(sigpar[2], omega1));
  my(a = eta1/(2*omega1));
  lambda^2 * (rig_raw_F1(sigpar, x, nmax)^2 - rig_raw_F(sigpar, x, nmax) * rig_raw_F2(sigpar, x, nmax))
    - 2*a*rig_raw_F(sigpar, x, nmax)^2;
};

rig_parity_det_kernel(sigpar, qstar, t, z, lmmax, nmax) =
{
  my(L = sigpar[2], z0 = sigpar[3], kappa = sigpar[4]);
  my(A = sigpar[5], B = sigpar[6]);
  my(omega1 = L[1]/2, omega3 = -L[2]/2);
  my(tau_mod = omega3/omega1, p = exp(Pi*I*tau_mod));
  my(lambda = Pi/(2*omega1));
  my(eta1 = ellzeta(L, omega1));
  my(a = eta1/(2*omega1));
  my(Csigma = 2*omega1/(Pi*somos4_theta1prime0(p, nmax)));
  my(gamma = lambda*kappa/2, x0 = lambda*z0);
  my(Xstar = B*t/qstar * exp(2*a*z0*kappa));
  my(total = 0);
  for (eps = 0, 1,
    my(R0 = 0, R1 = 0, D0 = 0, D1 = 0);
    for (ell = -lmmax, lmmax,
      my(term = exp(2*I*ell*x0) * somos4_theta_aell_direct(sigpar, ell, nmax)
        * somos4_theta_parity_sum(eps, Xstar * exp(2*I*ell*gamma), p, nmax));
      if (((ell % 2 + 2) % 2) == 0, R0 += term, R1 += term);
    );
    for (m = -lmmax, lmmax,
      my(term = somos4_theta_aell_direct(sigpar, m, nmax)
        * somos4_theta_parity_sum(eps, z * exp(2*I*m*gamma), p, nmax));
      if (((m % 2 + 2) % 2) == 0, D0 += term, D1 += term);
    );
    total += R1*D0 - R0*D1;
  );
  4 * lambda^2 * somos4_theta_Delta(p, nmax) * A^2 * Csigma^4 * exp(2*a*z0^2) * total;
};

rig_print_banner(title) =
{
  print("============================================================");
  print(title);
  print("============================================================");
};

rig_check_tuple(name, sigpar) =
{
  my(nsamp = 1025, fourier_nmax = 28, coeff_nmax = 28, max_ell = 8, max_fourier_A = 0, max_fourier_B = 0,
     max_closed_B = 0, max_antisym = 0, qstar, tuples_t, tuples_z, truncs, max_kernel_series = 0,
     max_kernel_coeff = 0, max_parity_det = 0, direct, theta, detk, coeffprobe, err);

  print("Tuple: ", name);

  for (ell = 0, max_ell,
    my(a_four = rig_coeff_even(rig_expr_A, sigpar, ell, fourier_nmax, nsamp));
    my(a_code = somos4_theta_aell_direct(sigpar, ell, fourier_nmax));
    max_fourier_A = max(max_fourier_A, abs(a_four + a_code));

    my(b_four = rig_coeff_even(rig_expr_B, sigpar, ell, fourier_nmax, nsamp));
    my(b_code = somos4_theta_bell_convolution(sigpar, ell, fourier_nmax));
    max_fourier_B = max(max_fourier_B, abs(b_four + b_code));

    my(L = sigpar[2], omega1 = L[1]/2, omega3 = -L[2]/2);
    my(p = exp(Pi*I*(omega3/omega1)), lambda = Pi/(2*omega1), eta1 = ellzeta(L, omega1), a = eta1/(2*omega1));
    my(T = if (ell % 2 == 0, somos4_theta2_const(p, coeff_nmax), somos4_theta3_const(p, coeff_nmax)));
    my(DT = if (ell % 2 == 0, somos4_Dp_theta2_const(p, coeff_nmax), somos4_Dp_theta3_const(p, coeff_nmax)));
    my(b_closed = (4*lambda^2*DT/T - 2*a) * somos4_theta_aell_direct(sigpar, ell, coeff_nmax));
    max_closed_B = max(max_closed_B, abs(b_code - b_closed));
  );

  for (ell = 0, 4,
    for (m = ell + 1, 8,
      my(L = sigpar[2], omega1 = L[1]/2, omega3 = -L[2]/2);
      my(p = exp(Pi*I*(omega3/omega1)), lambda = Pi/(2*omega1));
      my(al = somos4_theta_aell_direct(sigpar, ell, coeff_nmax));
      my(am = somos4_theta_aell_direct(sigpar, m, coeff_nmax));
      my(rhs = 4*lambda^2*al*am*somos4_theta_Delta(p, coeff_nmax)*(((ell % 2 + 2) % 2)-((m % 2 + 2) % 2)));
      max_antisym = max(max_antisym, abs(somos4_theta_antisymmetric_coeff(sigpar, ell, m, coeff_nmax) - rhs));
    );
  );

  qstar = somos4_theta_qstar(sigpar);
  tuples_t = [1/10, 1/12, 2/25];
  tuples_z = [6/5, 7/6, 5/4];
  truncs = [[8, 18], [10, 20], [12, 24]];

  for (idx = 1, #tuples_t,
    my(t = tuples_t[idx], z = tuples_z[idx]);
    direct = somos4_kernel_direct(sigpar, qstar, t, z, 24);
    for (j = 1, #truncs,
      my(lmmax = truncs[j][1], nmax = truncs[j][2]);
      theta = somos4_kernel_theta_series(sigpar, qstar, t, z, lmmax, nmax);
      detk = rig_parity_det_kernel(sigpar, qstar, t, z, lmmax, nmax);
      max_kernel_series = max(max_kernel_series, abs(direct - theta));
      max_parity_det = max(max_parity_det, abs(direct - detk));
      coeffprobe = somos4_probe_theta_coefficients(sigpar, qstar, t, 7, lmmax, nmax);
      for (k = 1, #coeffprobe,
        err = coeffprobe[k][4];
        max_kernel_coeff = max(max_kernel_coeff, err);
      );
    );
  );

  print(["max_fourier_A_signcheck", max_fourier_A]);
  print(["max_fourier_B_vs_code", max_fourier_B]);
  print(["max_closed_B_vs_code", max_closed_B]);
  print(["max_antisym_vs_closed", max_antisym]);
  print(["max_kernel_coeff_error", max_kernel_coeff]);
  print(["max_kernel_series_error", max_kernel_series]);
  print(["max_parity_det_error", max_parity_det]);

  if (max_fourier_A > 1e-45, error(Str("A Fourier check too large for ", name)));
  if (max_fourier_B > 1e-40, error(Str("B Fourier check too large for ", name)));
  if (max_closed_B > 1e-30, error(Str("Closed b_l check too large for ", name)));
  if (max_antisym > 1e-28, error(Str("Antisymmetric check too large for ", name)));
  if (max_kernel_coeff > 1e-16, error(Str("Kernel coefficient check too large for ", name)));
  if (max_kernel_series > 1e-16, error(Str("Kernel theta-series check too large for ", name)));
  if (max_parity_det > 1e-16, error(Str("Parity determinant check too large for ", name)));
  print("[PASS] tuple completed");
};

{
  default(realprecision, 160);
  rig_print_banner("Theta-Kernel Rigorous PARI Double-Check");
  rig_check_tuple("(1,1,1,1,1)", somos4_sigma_parameters(1,1,1,1,1));
  rig_check_tuple("(2,1,1,3,2)", somos4_sigma_parameters(2,1,1,3,2));
  print("------------------------------------------------------------");
  print("[DONE] all rigorous checks passed");
}

quit;