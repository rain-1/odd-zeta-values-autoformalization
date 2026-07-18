(* Verify the 6-fold summand transcription numerically, then size the Annihilator. *)
Get["/home/ubuntu/riscergosum/RISC/HolonomicFunctions.m"];
Print["HFload=", Head[Annihilator[nn!,{S[nn]}]]===List];
gB[x_,y_]:=Gamma[x]Gamma[y]/Gamma[x+y];
(* full unfolded summand F(n;a,b,c,d,k,j) *)
summ[n_,a_,b_,c_,d_,k_,j_]:=
  Binomial[n+a,a] Binomial[n+b,b] Binomial[n+c,c] Binomial[n+d,d]*
  (-1)^k Binomial[a+b,k] gB[n+1+k,n+1]^2*
  (-1)^j Binomial[b+c,j] gB[n+j+1,n+1] gB[n+j+1,n+d+1]*
  gB[n+a+b+1,n+1] gB[2 n+2+a+b+c+d,n+1] gB[n+b+c+d+1,n+1];
(* numeric partial sum for n=1, indices 0..NN, inner k,j full range *)
nval=1; NN=14;
tot=Sum[
   If[a+b>=0 && b+c>=0,
     Sum[summ[nval,a,b,c,d,k,j],{k,0,a+b},{j,0,b+c}],0],
   {a,0,NN},{b,0,NN},{c,0,NN},{d,0,NN}];
Print["n=1 partial sum (N=",NN,") = ",N[tot,20]];
Print["I_1 target ~ 3.2070e-5"];
Exit[];
