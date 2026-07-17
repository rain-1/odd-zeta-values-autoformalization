(* ============================================================================
   ZETA(7) LEADING-COEFFICIENT RECURRENCE via HolonomicFunctions
   Cell sigma=(10,2,4,1,6,3,8,5,9,7), M_{0,10}, weight 7.
   q_n = A_sigma(n) = [x1^n..x8^n] Prod_i W_i^n  (McCarthy-Osburn-Straub diagonal).
   Verified q_0..q_3 = 1, 61, 52921, 94357501 (matches BZ + is the NEW q_3).

   GOAL: the linear recurrence in n satisfied by q_n  ->  characteristic polynomial
   (asymptotic rates)  ->  propagate P_n (P_0=0,P_1=220,P_2=6021219/32) -> P_3.

   Run in the Mathematica 15 GUI (more RAM / interactive). Load HolonomicFunctions,
   then try the methods in order of expected speed. Watch MemoryInUse[].
   ============================================================================ *)

SetDirectory["/home/ubuntu/riscergosum/RISC"];        (* adjust if needed *)
AppendTo[$Path, "/home/ubuntu/riscergosum"];
AppendTo[$Path, "/home/ubuntu/riscergosum/RISC"];
Get["HolonomicFunctions.m"];

W  = {x2+x3, x2+x3+x4+x5, x3+x4+x5, x3+x4+x5+x6+x7, x5+x6+x7, x7+x8,
      x1+x2+x3+x4+x5+x6+x7+x8, x1+x2+x3};
xs = {x1,x2,x3,x4,x5,x6,x7,x8};

(* q_n = residue (2pi i)^-8 oint (Prod W)^n / (Prod x)^(n+1) dx.
   Integrand as a hyperexponential-in-x, hypergeometric-in-n object: *)
H = Exp[nn*(Sum[Log[W[[i]]],{i,8}] - Sum[Log[xs[[j]]],{j,8}])]/Product[xs[[j]],{j,8}];

(* ---- METHOD A: full annihilator + Takayama (all 8 integrations at once) ---- *)
ann = Annihilator[H, Join[{S[nn]}, Der/@xs]];          (* fast: 8 first-order ops *)
Print["annihilator ready, ", Length[ann], " ops"];
recA = Takayama[ann, xs];                                (* HEAVY: the Groebner step *)
Print["Takayama recurrence:"]; Print[recA];

(* ---- METHOD B (if A too heavy): integrate variables ONE AT A TIME ----
   iterate CreativeTelescoping, eliminating x1, then x2, ... keeping the rest + nn.
   Often far less memory than all-at-once. Pseudocode: *)
(*
  cur = ann;
  Do[ ct = CreativeTelescoping[cur, Der[xs[[k]]], DeleteCases[Join[{S[nn]},Der/@xs], Der[xs[[k]]]]];
      cur = ct[[1]];  (* the telescoper ideal, now free of xs[[k]] *)
      Print["eliminated ", xs[[k]], " ; ops ", Length[cur]],
    {k, 8}];
  Print[cur];
*)

(* ---- METHOD C: Hermite-reduction CT (Bostan et al.), often fastest for integrals,
   applied iteratively per variable via Method -> "Hermite". ---- *)

(* CERTIFICATE CHECK once a recurrence rec (order r, coeffs c_k(n)) is found:
   it must annihilate q_0..q_30 below. *)
qvals = {1, 61, 52921, 94357501, 235634763001, 715362962769061, 2467090298135229481,
   9307547697979861686781, 37534429062230228638731001, 159353643933835371998356995061,
   704783363364126892491454202797921, 3222628604089447767490220153824054501,
   15148413884323790615228008825002694961641, 72886254017639273321994250167935263062755701,
   357746089392600352149002550465733890885694342921,
   1786417921593123386661623964552227634515708049877501,
   9055684571885781620954177252229432687991911159347886841,
   46516872145977694095333102659963791863052205106745281424021,
   241770462117232054920814654346637479094416751507551078479603921};
(* validate: ApplyOreOperator[recA[[1]], q[nn]] /. q->(qvals[[#+1]]&) == 0 for all shifts *)
