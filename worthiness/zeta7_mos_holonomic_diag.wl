(* READY once HolonomicFunctions.m available. Computes the recurrence for
   q_n = A_sigma(n) = [x1^n..x8^n] prod_i W_i^n  (leading coeff, BZ zeta(7) cell).
   The diagonal of a rational function is holonomic; CT gives the recurrence. *)
Get["HolonomicFunctions.m"];
(* q_n = constant term of F^n where F = prod W_i / prod x_j : *)
Ws={x2+x3, x2+x3+x4+x5, x3+x4+x5, x3+x4+x5+x6+x7, x5+x6+x7, x7+x8,
    x1+x2+x3+x4+x5+x6+x7+x8, x1+x2+x3};
xs={x1,x2,x3,x4,x5,x6,x7,x8};
(* Use the generating function / annihilator of F^n via CT.
   HolonomicFunctions: build annihilator of the rational integrand and telescope. *)
Fnum=Times@@Ws; Fden=Times@@xs;
(* q_n = CT_x (Fnum/Fden)^n ; represent as constant term, apply CreativeTelescoping *)
(* Following the paper (Prop A86 method): use the diagonal via Annihilator of the
   summand of the equivalent binomial sum, or directly the multivariate residue. *)
Print["Set up. Use CreativeTelescoping on the rational form to get the n-recurrence."];
(* Practical route mirroring the paper: feed the explicit binomial multi-sum
   summand (once extracted) to Annihilator+CreativeTelescoping. *)
