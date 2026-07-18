(* Period-level multi-sum creative telescoping for I_n (Barnes 6-fold sum).
   Summand F(n;a,b,c,d,k,j) is proper hypergeometric in all 7 vars.
   Compute Annihilator, then iterated discrete CT eliminating k,j,d,c,b,a. *)
dir="/home/ubuntu/fable-episode-2/zeta-math/worthiness/ct_run/";
lf=OpenWrite[dir<>"barnes_ct.log",Appended->True];
log[x__]:=(WriteString[lf,x,"\n"];Flush[lf]);
log["==== BARNES CT ",DateString[]," ===="];
Get["/home/ubuntu/riscergosum/RISC/HolonomicFunctions.m"];
If[Head[Annihilator[nn!,{S[nn]}]]=!=List, log["FATAL load"];Close[lf];Exit[]];
log["HF ok ",DateString[]];
gB[x_,y_]:=Gamma[x]Gamma[y]/Gamma[x+y];
summand=
  Binomial[nn+a,a] Binomial[nn+b,b] Binomial[nn+c,c] Binomial[nn+d,d]*
  (-1)^k Binomial[a+b,k] gB[nn+1+k,nn+1]^2*
  (-1)^j Binomial[b+c,j] gB[nn+j+1,nn+1] gB[nn+j+1,nn+d+1]*
  gB[nn+a+b+1,nn+1] gB[2 nn+2+a+b+c+d,nn+1] gB[nn+b+c+d+1,nn+1];
gens={S[a],S[b],S[c],S[d],S[k],S[j],S[nn]};
t0=AbsoluteTime[];
ann=Annihilator[summand, gens];
log["Annihilator ready: ",Length[ann]," ops in ",Round[AbsoluteTime[]-t0],"s; ByteCount=",ToString[ByteCount[ann]]," ",DateString[]];
DumpSave[dir<>"barnes_ann.mx",{ann,gens,summand}];
(* iterated discrete CT: eliminate innermost finite indices first *)
elim={k,j,d,c,b,a};
cur=ann; rem=gens;
TCAP=9000; MCAP=12*10^9;
Do[ dop=S[u]-1; t1=AbsoluteTime[];
    log["-- start elim ",ToString[u]," ",DateString[]];
    res=TimeConstrained[MemoryConstrained[
          CreativeTelescoping[cur,dop,DeleteCases[rem,S[u]]], MCAP,$Failed],
          TCAP,$TimedOut];
    dt=Round[AbsoluteTime[]-t1];
    If[res===$TimedOut||res===$Failed||Head[res]=!=List,
      log["!! elim ",ToString[u]," ABORTED after ",dt,"s result=",ToString[res]];
      log["STOP at var ",ToString[u]]; Close[lf]; Exit[]];
    cur=res[[1]]; rem=DeleteCases[rem,S[u]];
    DumpSave[dir<>"barnes_after_"<>ToString[u]<>".mx",{cur,rem,elim,u}];
    log["** elim ",ToString[u]," DONE in ",dt,"s; #tele=",ToString[Length[cur]],
        "; ByteCount=",ToString[ByteCount[cur]]," ",DateString[]],
  {u,elim}];
rec=If[Head[cur]===List, cur[[1]], cur];
log["ALL ELIMS DONE. TELESCOPER (InputForm):"]; log[ToString[InputForm[rec]]];
DumpSave[dir<>"barnes_final.mx",{cur,rem}];
applied=ApplyOreOperator[rec,I[nn]];
ordG=Max[Cases[applied,I[nn+aa_.]:>aa,Infinity]/.{}->{0}];
log["order=",ToString[ordG]];
coeffs=Table[Coefficient[applied,I[nn+kk]],{kk,0,ordG}];
D0=Max[Exponent[coeffs,nn]];
log["degree=",ToString[D0]];
Do[log["COEF c_",ToString[kk],"(n) = ",ToString[InputForm[coeffs[[kk+1]]]]],{kk,0,ordG}];
log["DONE ",DateString[]]; Close[lf]; Exit[];
