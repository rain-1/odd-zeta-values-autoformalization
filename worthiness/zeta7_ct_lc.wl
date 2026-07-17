(* Iterated creative telescoping of the LOW-COUPLING W_lc diagonal for zeta(7) q_n.
   W_lc = {1,2},{1,2,3,4},{2,3,4,5},{3,4,5},{4,5,6},{4,5,6,7},{5,6,7,8},{7,8}
   Max window size 4, NO full-width coupler. This is the untested "Plan B". *)
lf=OpenWrite["zeta7_ct_lc.log"]; log[x__]:=(WriteString[lf,x,"\n"];Flush[lf]);
log["START ",DateString[]];
Get["/home/ubuntu/riscergosum/RISC/HolonomicFunctions.m"];
If[Head[Annihilator[nn!,{S[nn]}]]=!=List, log["FATAL load"];Close[lf];Exit[]];
log["HF ok ",DateString[]];
W={x1+x2, x1+x2+x3+x4, x2+x3+x4+x5, x3+x4+x5, x4+x5+x6, x4+x5+x6+x7,
   x5+x6+x7+x8, x7+x8};
xs={x1,x2,x3,x4,x5,x6,x7,x8};
H=Exp[nn*(Sum[Log[W[[i]]],{i,8}]-Sum[Log[xs[[j]]],{j,8}])]/Product[xs[[j]],{j,8}];
t0=AbsoluteTime[];
ann=Annihilator[H,Join[{S[nn]},Der/@xs]];
log["ann ready ",Length[ann]," ops in ",Round[AbsoluteTime[]-t0],"s ",DateString[]];
(* elimination order: fewest-incidence variables first *)
elimOrder={x1,x8,x2,x6,x3,x7,x4,x5};
cur=ann; rem=Join[{S[nn]},Der/@xs];
Do[ dx=Der[v]; t1=AbsoluteTime[];
    ct=CreativeTelescoping[cur,dx,DeleteCases[rem,dx]];
    cur=ct[[1]]; rem=DeleteCases[rem,dx];
    DumpSave["zeta7_lc_cur.mx",{cur,rem,elimOrder,v}];
    log["elim ",ToString[v]," in ",Round[AbsoluteTime[]-t1],"s; #tele=",ToString[Length[cur]]," ",DateString[]],
  {v,elimOrder}];
rec=If[Head[cur]===List, cur[[1]], cur];
log["RECURRENCE (InputForm):"]; log[ToString[InputForm[rec]]];
applied=ApplyOreOperator[rec,q[nn]];
ordG=Max[Cases[applied,q[nn+a_.]:>a,Infinity]/.{}->{0}];
log["order=",ToString[ordG]];
coeffs=Table[Coefficient[applied,q[nn+k]],{k,0,ordG}];
degs=Exponent[coeffs,nn]; D0=Max[degs];
log["degree=",ToString[D0]];
charpoly=Sum[Coefficient[coeffs[[k+1]],nn,D0]*lam^k,{k,0,ordG}];
log["charpoly (leading, D=",ToString[D0],"): ",ToString[InputForm[charpoly]]];
log["char roots: ",ToString[InputForm[N[lam/.Solve[charpoly==0,lam],20]]]];
(* dump coefficient polynomials for external certification *)
Do[log["COEF c_",ToString[k],"(n) = ",ToString[InputForm[coeffs[[k+1]]]]],{k,0,ordG}];
log["DONE ",DateString[]]; Close[lf]; Exit[];
