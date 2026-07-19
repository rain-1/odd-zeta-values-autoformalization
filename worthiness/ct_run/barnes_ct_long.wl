(* Barnes 6-fold CT — LONG-CAP resume (2026-07-19). Loads barnes_ann.mx (or the
   latest barnes_after_<var>.mx checkpoint) and continues the iterated discrete
   CT with 12h/step, 9GB caps. Same math as barnes_ct.wl. *)
dir="/home/ubuntu/fable-episode-2/zeta-math/worthiness/ct_run/";
lf=OpenWrite[dir<>"barnes_long.log",Appended->True];
log[x__]:=(WriteString[lf,x,"\n"];Flush[lf]);
log["==== BARNES CT LONG ",DateString[]," ===="];
Get["/home/ubuntu/riscergosum/RISC/HolonomicFunctions.m"];
If[Head[Annihilator[nn!,{S[nn]}]]=!=List, log["FATAL load"];Close[lf];Exit[]];
log["HF ok ",DateString[]];
elim={k,j,d,c,b,a};
done=0;
Do[If[FileExistsQ[dir<>"barnes_after_"<>ToString[elim[[i]]]<>".mx"],done=i],
   {i,Length[elim]}];
If[done==0,
  Get[dir<>"barnes_ann.mx"]; cur=ann; rem=gens,
  Get[dir<>"barnes_after_"<>ToString[elim[[done]]]<>".mx"]];
log["resume: done=",ToString[done]," (",ToString[Take[elim,done]],
    "); #tele=",ToString[Length[cur]],"; ByteCount=",ToString[ByteCount[cur]]];
TCAP=43200; MCAP=9*10^9;
Do[ u=elim[[i]]; dop=S[u]-1; t1=AbsoluteTime[];
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
  {i,done+1,Length[elim]}];
rec=If[Head[cur]===List, cur[[1]], cur];
log["ALL ELIMS DONE. TELESCOPER (InputForm):"]; log[ToString[InputForm[rec]]];
DumpSave[dir<>"barnes_final.mx",{cur,rem}];
applied=ApplyOreOperator[rec,ff[nn]];
ordG=Max[Cases[applied,ff[nn+aa_.]:>aa,Infinity]/.{}->{0}];
log["order=",ToString[ordG]];
coeffs=Table[Coefficient[applied,ff[nn+kk]],{kk,0,ordG}];
D0=Max[Exponent[coeffs,nn]];
log["degree=",ToString[D0]];
Do[log["COEF c_",ToString[kk],"(n) = ",ToString[InputForm[coeffs[[kk+1]]]]],
   {kk,0,ordG}];
log["DONE ",DateString[]]; Close[lf]; Exit[];
