(* exact port of zeta7_barnes_num1.py 4-fold all-positive summand *)
BB[a_,b_]:=Gamma[a] Gamma[b]/Gamma[a+b];
G2[p_,n_]:=Sum[(-1)^k Binomial[p,k] BB[n+1+k,n+1]^2,{k,0,p}];
H2[q_,r_,n_]:=Sum[(-1)^j Binomial[q,j] BB[n+j+1,n+1] BB[n+j+1,n+r+1],{j,0,q}];
term[a_,b_,c_,d_,n_]:=Binomial[n+a,a]Binomial[n+b,b]Binomial[n+c,c]Binomial[n+d,d]*
   G2[a+b,n] H2[b+c,d,n] BB[n+a+b+1,n+1] BB[2n+2+a+b+c+d,n+1] BB[n+b+c+d+1,n+1];
(* numeric gate: n=0 partial sum should approach 3.5554 *)
part[n_,NN_]:=Sum[term[a,b,c,d,n],{a,0,NN},{b,0,NN},{c,0,NN},{d,0,NN}];
Print["I0 partial N=12: ", N[part[0,12],10], "  (exact 3.55544...)"];
Print["I1 partial N=12: ", N[part[1,12],10], "  (exact 3.2071e-5)"];
(* try: can Mathematica close the sum over d symbolically (fixed a,b,c,n symbolic)? *)
sd = TimeConstrained[Sum[Binomial[n+d,d] H2[b+c,d,n] BB[2n+2+a+b+c+d,n+1] BB[n+b+c+d+1,n+1],{d,0,Infinity}], 60];
Print["sum over d (symbolic) head: ", Head[sd]];
Print[sd//Short];
