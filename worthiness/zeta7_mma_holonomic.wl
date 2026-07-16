(* READY-TO-RUN once HolonomicFunctions.m is available.
   Place HolonomicFunctions.m on $Path (or Get its full path), then run:
     echo '<< "/…/zeta7_mma_holonomic.wl"' | wolfram -noprompt

   Goal: creative telescoping of the exact 4-fold all-positive summand of I_n to
   get the order-~4 recurrence in n (ATTACK 2), then feed q_n data to guess/RSolve.
   We use the FULLY EXPANDED pure-hypergeometric 7-fold summand (HolonomicFunctions
   wants proper-hypergeometric terms). r-index pre-collapsed to a Beta to save one
   fold => 6-fold. *)

Get["HolonomicFunctions.m"];   (* adjust path if needed *)

(* pure-hypergeometric summand U(n; a,b,c,d,p,q) after r-collapse:
   B(x,y)=Gamma[x]Gamma[y]/Gamma[x+y]; all args linear in the indices. *)
BB[x_,y_] := Gamma[x] Gamma[y]/Gamma[x+y];
U = Binomial[n+a,a] Binomial[n+b,b] Binomial[n+c,c] Binomial[n+d,d] *
    (-1)^(p+q) Binomial[a+b,p] Binomial[b+c,q] *
    BB[n+p+1,n+1]^2 BB[n+a+b+1,n+1] BB[2n+2+a+b+c+d,n+1] *
    BB[n+b+c+d+1,n+1] BB[n+q+1,n+1] BB[n+q+1,n+d+1];

(* Annihilating operators in each summation variable + n, via HolonomicFunctions.
   Then CreativeTelescoping eliminating a,b,c,d,p,q one at a time, keeping n. *)
ann = Annihilator[U, {S[a],S[b],S[c],S[d],S[p],S[q],S[n]}];
Print["Annihilator computed: ", Length[ann], " operators"];

(* eliminate the six summation shifts; produce telescoper in S[n] *)
ct = CreativeTelescoping[U, {S[a],S[b],S[c],S[d],S[p],S[q]}, {S[n]}];
Print["Telescoper (recurrence in n): "];
Print[ct[[1]]];
Print["order in n = ", Exponent[ct[[1]] /. S[n]->x, x]];
