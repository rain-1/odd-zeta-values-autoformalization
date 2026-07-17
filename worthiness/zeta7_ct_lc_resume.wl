(* Resume W_lc iterated CT from the last checkpoint (zeta7_lc_cur.mx). *)
lf=OpenWrite["zeta7_ct_lc.log",Appended->True]; log[x__]:=(WriteString[lf,x,"\n"];Flush[lf]);
log["RESUME ",DateString[]];
Get["/home/ubuntu/riscergosum/RISC/HolonomicFunctions.m"];
If[Head[Annihilator[nn!,{S[nn]}]]=!=List, log["FATAL load"];Close[lf];Exit[]];
log["HF ok ",DateString[]];
Get["zeta7_lc_cur.mx"];  (* restores cur, rem, elimOrder, v (last eliminated) *)
log["checkpoint loaded; last elim was ",ToString[v],"; #tele=",ToString[Length[cur]]];
done=Position[elimOrder,v][[1,1]];
remaining=Drop[elimOrder,done];
log["remaining elims: ",ToString[remaining]];
Do[ dx=Der[u]; t1=AbsoluteTime[];
    ct=CreativeTelescoping[cur,dx,DeleteCases[rem,dx]];
    cur=ct[[1]]; rem=DeleteCases[rem,dx];
    DumpSave["zeta7_lc_cur.mx",{cur,rem,elimOrder,u}];
    log["elim ",ToString[u]," in ",Round[AbsoluteTime[]-t1],"s; #tele=",ToString[Length[cur]]," ",DateString[]],
  {u,remaining}];
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
Do[log["COEF c_",ToString[k],"(n) = ",ToString[InputForm[coeffs[[k+1]]]]],{k,0,ordG}];
log["DONE ",DateString[]]; Close[lf]; Exit[];
