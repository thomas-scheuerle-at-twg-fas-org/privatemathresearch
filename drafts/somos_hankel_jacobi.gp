/*
  somos_hankel_jacobi.gp

  PARI/GP companion to:
    Thomas Scheuerle and Michael Somos,
    "A Somos-Type Constraint on Hankel Determinants and Jacobi
     Recurrence Coefficients", 31 August 2026.

  The comments below refer to sections and equation numbers in that paper.

  PURPOSE
  -------
  Given Somos parameters p1, p2, the first integral p4, Michael Somos's
  orbit convention p3 = -a4/a2, and nextra, construct N = 4+nextra terms.

  We normalize a1=a2=1.  Then p3=-a4/a2 gives a4=-p3.  If r=a3, the
  two determinant quotients are
       b_2 = a1*a3/a2^2 = r,
       b_3 = a2*a4/a3^2 = -p3/r^2.
  Requiring the invariant biquadratic (paper (33), (46)) gives
       p1*r^3 + p2*r^2 + p4*p3*r + p3^2 - p1*p3 = 0.
  Thus p3 selects the remaining orbit freedom while p4 selects the
  invariant curve.  A particular root r selects a branch/orbit.

  OUTPUTS
  -------
   1. Stieltjes continued-fraction coefficients d(k), using the canonical
      factorization d(0)=1, d(2j-1)=b_j and d(2j)=1.  This is a concrete lift of
      b_j=d(2j-1)d(2j); compare Sections 11, 11.1 and equations (38)-(40).
   2. Monic orthogonal polynomials for the normalized shifted functional
      of paper (10)-(11), obtained directly from its moments.
   3. Moment sequence and its truncated generating series, from the
      Stieltjes fraction (paper (2), (36)).
   4. First-shifted Hankel determinants a_n=Delta_n^(1), paper (3)-(5),
      together with a check of the Somos-4 recurrence (28)/(44).
   5. Optional algebraic generating-function guess via seralgdep.
   6. Formal orthogonality data: Jacobi alpha/beta coefficients, norms,
      and the moment-functional statement.  Positivity and a genuine
      positive Borel measure require extra hypotheses; see Remark 4.

  CALL
  ----
    somos_hankel_jacobi(p1,p2,p3,p4,nextra)
    somos_hankel_jacobi(p1,p2,p3,p4,nextra,r0)

  If r0 is omitted, r is represented exactly as Mod(r,C(r)), where C is
  the cubic above.  Supply a chosen nonzero root r0 (usually rational or
  algebraic) to select a particular branch.  Example corresponding to the
  normalized classical seed (1,1,2,3):

    somos_hankel_jacobi(1,1,-3,4,8,2)

  PARI/GP note: seralgdep(s,p,r) searches for a polynomial relation of
  degree <=p in the dependent variable and coefficient degree <=r.
  The series variable is y because seralgdep reserves x for its result.
*/

\p 80

/* Coefficient vector [m_0,...,m_{M-1}] -> series in y. */
vec_to_ser(v, M) = {
  my(s = O(y^M));
  for(k=1, min(#v,M), s += v[k]*y^(k-1));
  s;
};

/* Resolve a finite S-fraction backwards, to precision O(y^M):
      1/(1-d0*y/(1-d1*y/(...))).
   With sufficiently many d's, its first M coefficients equal the formal
   infinite-fraction moments. */
sfraction_series(d, M) = {
  my(F = 1 + O(y^M));
  forstep(k=#d, 1, -1, F = 1/(1 - d[k]*'y*F));
  F;
};

/* Hankel determinant det(m_{i+j+shift}), i,j=0..n-1.
   GP vectors are 1-based, hence moment m_q is mv[q+1]. */
hankel_det(mv, n, shift) = {
  if(n==0, return(1));
  matdet(matrix(n,n,i,j, mv[i+j+shift-1]));
};

/* Inner product induced by moments mv=[m0,m1,...]. */
inner_moment(P,Q,mv) = {
  my(dp=poldegree(P), dq=poldegree(Q), z=0);
  for(i=0,dp, for(j=0,dq,
    z += polcoef(P,i,'t)*polcoef(Q,j,'t)*mv[i+j+1]
  ));
  z;
};

/* Monic OPs for a normalized moment vector nu=[nu0,nu1,...], nu0=1.
   P_k=t^k+sum_{j<k} c_j t^j and G*c=-v. */
monic_ops(nu, K) = {
  my(P=vector(K+1), G, rhs, cc, pk);
  P[1]=1;
  for(k=1,K,
    G=matrix(k,k,i,j,nu[i+j-1]);
    rhs=vector(k,i,-nu[k+i])~;
    cc=matsolve(G,rhs);
    pk=t^k;
    for(j=1,k, pk += cc[j]*t^(j-1));
    P[k+1]=pk;
  );
  P;
};

/* Conservative seralgdep search.  A returned relation R(x,y) means
   R(S(y),y)=O(y^M).  It is evidence, not a proof, unless verified
   independently from the recurrence. */
guess_algebraic(S, maxpow=4, maxdeg=8) = {
  my(R=0);
  for(p=2,maxpow,
    for(r=4,maxdeg,
      R=seralgdep(S,p,r);
      if(R!=0, return([p,r,R,subst(R,x,S)]));
    )
  );
  0;
};

somos_hankel_jacobi(p1,p2,p3,p4,nextra,r0=0) = {
  my(N=4+nextra, M, C, rr, b, d, S, mu, nu, OP, H, A, norms,
     alpha, beta, alg, ok=1, lhs, formal_measure, n);

  if(nextra<0, error("nextra must be >= 0, since N=4+nextra."));
  if(p1==0 && p2==0, error("Degenerate choice p1=p2=0 is not supported."));

  C = p1*r^3 + p2*r^2 + p4*p3*r + p3^2 - p1*p3;
  if(r0==0,
    rr = Mod(r,C),
    rr = r0;
    if(subst(C,r,rr)!=0,
      error("The supplied r0 does not satisfy the orbit cubic C(r)=0."));
  );
  if(rr==0, error("The selected root r=a3 must be nonzero."));

  /* Need moments through mu_(2N-1), plus spare precision for seralgdep. */
  M = max(2*N+8,32);

  /* Shifted Jacobi coefficients b_j.  The paper's Somos constraint starts
     at b_2,b_3; b_1=1 enforces the normalization a1=a2=1. */
  b = vector(M+2);
  b[1]=1; b[2]=rr; b[3]=-p3/rr^2;
  if(b[3]==0, error("p3=0 makes b3=0; quasi-definiteness fails."));
  for(j=3,#b-1,
    /* paper (48), equivalently (43): b_{j-1} b_j^2 b_{j+1}=p1 b_j+p2 */
    b[j+1]=(p1*b[j]+p2)/(b[j-1]*b[j]^2);
    if(b[j+1]==0, error(Str("Zero Jacobi coefficient at b_",j+1,".")));
  );

  /* Canonical continued-fraction lift.  d[1] is d(0) in the paper/OEIS. */
  d = vector(2*M+2,k, if(k==1,1,if(k%2,1,b[k/2])));

  print("\n1. Continued-fraction coefficients d(k), k=0..",2*N+1);
  print(vector(2*N+2,k,d[k]));
  print("   Contracted shifted Jacobi b_j=d(2j-1)d(2j), j=1..",N+1);
  print(vector(N+1,j,d[2*j]*d[2*j+1]));

  S = sfraction_series(d,M);
  mu = vector(M,k,polcoef(S,k-1,'y));
  if(mu[2]==0,error("mu_1=0, so the shifted normalization is undefined."));
  nu = vector(M-1,k,mu[k+1]/mu[2]);

  print("\n3. Moments mu_0..mu_",2*N-1);
  print(vector(2*N,k,mu[k]));
  /* print("   Truncated generating series S(y):"); */
  /* print(S); */

  /* OP degree N needs normalized shifted moments through index 2N. */
  OP = monic_ops(nu,N);
  print("\n2. Monic orthogonal polynomials P_hat_0..P_hat_",N);
  for(k=0,N, print("P_hat_",k,"(t) = ",OP[k+1]));

  A=vector(N,n,hankel_det(mu,n,1));
  print("\n4. Shifted Hankel/Somos sequence a_1..a_",N);
  print(A);
  if(N>=4,
    for(k=1,N-4,
      lhs=A[k+4]*A[k]-p1*A[k+3]*A[k+1]-p2*A[k+2]^2;
      if(lhs!=0,ok=0);
    )
  );
  print("   Seed convention check: -a4/a2 = ",-A[4]/A[2]," (requested p3=",p3,")");
  print("   Somos recurrence check through available terms: ",if(ok,"OK","FAILED"));

  alg=guess_algebraic(S,4,min(10,N+2));
  print("\n5. seralgdep generating-function search");
  if(alg==0,
    print("No relation found in the searched bounds."),
    print("degree in S <= ",alg[1],", coefficient degree in y <= ",alg[2]);
    print("R(x,y) = ",alg[3]);
    print("verification R(S(y),y) = ",alg[4]);
  );

  norms=vector(N+1,k,inner_moment(OP[k],OP[k],nu));
  alpha=vector(N,k,
    inner_moment(t*OP[k],OP[k],nu)/norms[k]
  );
  beta=vector(N,k,if(k==1,0,norms[k]/norms[k-1]));

  print("\n6. Orthogonality data");
  print("Norms h_0..h_",N," = ",norms);
  print("Diagonal Jacobi coefficients alpha_0..alpha_",N-1," = ",alpha);
  print("Off-diagonal beta_1..beta_",N-1," (beta_0 shown as 0) = ",beta);
  formal_measure = Str("Lhat(t^k)=mu_(k+1)/mu_1, k>=0; ",
    "the displayed P_hat_n are orthogonal for this formal functional. ",
    "If all computed beta_n are positive under a real specialization, ",
    "the Jacobi data define the corresponding positive measure.");
  print(formal_measure);

  /* Return all data for programmatic use. */
  [d,b,mu,S,OP,A,alg,norms,alpha,beta,C,rr];
};
