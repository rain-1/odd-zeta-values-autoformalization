lf=OpenWrite["zeta5_ct.log"]; log[x__]:=(WriteString[lf,x,"\n"];Flush[lf]);
log["START ",DateString[]];
Get["/home/ubuntu/riscergosum/RISC/HolonomicFunctions.m"];
If[Head[Annihilator[nn!,{S[nn]}]]=!=List, log["FATAL load"];Close[lf];Exit[]];
log["HF ok"];
W={x1+x2+x3, x1+x2+x3+x4, x2+x3, x2+x3+x4+x5, x3+x4+x5+x6, x4+x5+x6};
xs={x1,x2,x3,x4,x5,x6};
H=Exp[nn*(Sum[Log[W[[i]]],{i,6}]-Sum[Log[xs[[j]]],{j,6}])]/Product[xs[[j]],{j,6}];
ann=Annihilator[H,Join[{S[nn]},Der/@xs]];
log["ann ready ",Length[ann]," ",DateString[]];
elim={x1,x6,x5,x2,x4,x3};
cur=ann; rem=Join[{S[nn]},Der/@xs];
Do[ dx=Der[v]; t1=AbsoluteTime[];
    r=TimeConstrained[MemoryConstrained[
        CreativeTelescoping[cur,dx,DeleteCases[rem,dx]], 9*10^9,"MEMCAP"],1200,"TIMECAP"];
    If[MatchQ[r,"MEMCAP"|"TIMECAP"],
       log["elim ",ToString[v]," HIT ",r," after ",Round[AbsoluteTime[]-t1],"s; MaxMem=",ToString[N[MaxMemoryUsed[]/10^9,3]],"GB"];Close[lf];Exit[]];
    cur=r[[1]]; rem=DeleteCases[rem,dx];
    log["elim ",ToString[v]," OK in ",Round[AbsoluteTime[]-t1],"s; #tele=",ToString[Length[cur]],"; MaxMem=",ToString[N[MaxMemoryUsed[]/10^9,3]],"GB ",DateString[]],
  {v,elim}];
rec=cur[[1]];
log["RECURRENCE: ",ToString[InputForm[rec]]];
applied=ApplyOreOperator[rec,q[nn]];
qvals={1,21,2989,714549,217515501,76157194521,29212502584861,11948862404417589,5126125209508057069,2281536711276290023521,1045602285620288110917489,490732751530592114892132729,234911488629087602651879253981,114340217747630397374352879383481,56451762782588305056295246156192989,28216409380697930719500315079964778549,14255855542175080990213317430274909298669};
qf[m_]:=qvals[[m+1]];
ordG=Max[Cases[applied,q[nn+a_.]:>a,Infinity]/.{}->{0}];
log["order=",ToString[ordG]];
res=Table[{k,Simplify[(applied/.nn->k)/.q[a_]:>qf[a]]},{k,0,16-ordG}];
log["cert residues: ",ToString[res]];
log["ALLZERO ",ToString[AllTrue[res,(#[[2]]===0)&]]];
coeffs=Table[Coefficient[applied,q[nn+k]],{k,0,ordG}];
D0=Max[Exponent[coeffs,nn]];
charpoly=Sum[Coefficient[coeffs[[k+1]],nn,D0]*lam^k,{k,0,ordG}];
log["charpoly (D=",ToString[D0],"): ",ToString[InputForm[Simplify[charpoly]]]];
log["char roots: ",ToString[InputForm[N[lam/.Solve[charpoly==0,lam],10]]]];
log["expected: 4lam^3-2368lam^2-188lam+1, roots ~592.08,0.005,-0.0844"];
log["DONE ",DateString[]];Close[lf];Exit[];
