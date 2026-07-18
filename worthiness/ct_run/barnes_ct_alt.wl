(* Fallback: reuse saved Barnes annihilator, try alternate elimination order.
   Set ORDER env-style by editing `elim` below. Does NOT recompute Annihilator. *)
dir="/home/ubuntu/fable-episode-2/zeta-math/worthiness/ct_run/";
lf=OpenWrite[dir<>"barnes_ct_alt.log",Appended->True];
log[x__]:=(WriteString[lf,x,"\n"];Flush[lf]);
log["==== BARNES CT ALT ",DateString[]," ===="];
Get["/home/ubuntu/riscergosum/RISC/HolonomicFunctions.m"];
If[Head[Annihilator[nn!,{S[nn]}]]=!=List, log["FATAL load"];Close[lf];Exit[]];
Get[dir<>"barnes_ann.mx"];  (* ann, gens, summand *)
log["ann loaded: ",Length[ann]," ops"];
(* ALTERNATE ORDER: try j first (most local: couples b,c,d,n), then k, then rest *)
elim={j,k,d,c,b,a};
cur=ann; rem=gens; TCAP=9000; MCAP=12*10^9;
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
    DumpSave[dir<>"barnes_alt_after_"<>ToString[u]<>".mx",{cur,rem,elim,u}];
    log["** elim ",ToString[u]," DONE in ",dt,"s; #tele=",ToString[Length[cur]],
        "; ByteCount=",ToString[ByteCount[cur]]," ",DateString[]],
  {u,elim}];
rec=If[Head[cur]===List, cur[[1]], cur];
log["ALL ELIMS DONE. TELESCOPER:"]; log[ToString[InputForm[rec]]];
applied=ApplyOreOperator[rec,I[nn]];
ordG=Max[Cases[applied,I[nn+aa_.]:>aa,Infinity]/.{}->{0}];
coeffs=Table[Coefficient[applied,I[nn+kk]],{kk,0,ordG}];
log["order=",ToString[ordG],"; degree=",ToString[Max[Exponent[coeffs,nn]]]];
Do[log["COEF c_",ToString[kk],"(n) = ",ToString[InputForm[coeffs[[kk+1]]]]],{kk,0,ordG}];
log["DONE ",DateString[]]; Close[lf]; Exit[];
