(* Resume W_lc iterated CT from checkpoint, guarded per-step. Absolute paths. *)
dir="/home/ubuntu/fable-episode-2/zeta-math/worthiness/ct_run/";
lf=OpenWrite[dir<>"resume.log",Appended->True];
log[x__]:=(WriteString[lf,x,"\n"];Flush[lf]);
log["==== RESUME ",DateString[]," ===="];
Get["/home/ubuntu/riscergosum/RISC/HolonomicFunctions.m"];
If[Head[Annihilator[nn!,{S[nn]}]]=!=List, log["FATAL load"];Close[lf];Exit[]];
log["HF ok ",DateString[]];
Get[dir<>"zeta7_lc_cur.mx"];  (* cur, rem, elimOrder, v *)
done=Position[elimOrder,v][[1,1]];
remaining=Drop[elimOrder,done];
log["loaded; last elim=",ToString[v],"; #tele=",ToString[Length[cur]],
    "; ByteCount=",ToString[ByteCount[cur]],"; remaining=",ToString[remaining]];
TCAP=10800; (* 3h per step *) MCAP=12*10^9;
Do[ dx=Der[u]; t1=AbsoluteTime[];
    log["-- start elim ",ToString[u]," ",DateString[]];
    res=TimeConstrained[MemoryConstrained[
          CreativeTelescoping[cur,dx,DeleteCases[rem,dx]], MCAP, $Failed],
          TCAP, $TimedOut];
    dt=Round[AbsoluteTime[]-t1];
    If[res===$TimedOut || res===$Failed || Head[res]=!=List,
      log["!! elim ",ToString[u]," ABORTED after ",dt,"s result=",ToString[res]];
      log["STOP at step ",ToString[done+1]," (var ",ToString[u],")"];
      Close[lf]; Exit[]];
    cur=res[[1]]; rem=DeleteCases[rem,dx]; v=u; done=done+1;
    DumpSave[dir<>"zeta7_lc_cur.mx",{cur,rem,elimOrder,v}];
    DumpSave[dir<>"ckpt_after_"<>ToString[u]<>".mx",{cur,rem,elimOrder,v}];
    log["** elim ",ToString[u]," DONE in ",dt,"s; #tele=",ToString[Length[cur]],
        "; ByteCount=",ToString[ByteCount[cur]]," ",DateString[]],
  {u,remaining}];
(* all eliminations done -> extract recurrence *)
rec=If[Head[cur]===List, cur[[1]], cur];
log["ALL ELIMS DONE. RECURRENCE (InputForm):"]; log[ToString[InputForm[rec]]];
DumpSave[dir<>"zeta7_ct_final.mx",{cur,rem,elimOrder}];
applied=ApplyOreOperator[rec,q[nn]];
ordG=Max[Cases[applied,q[nn+a_.]:>a,Infinity]/.{}->{0}];
log["order=",ToString[ordG]];
coeffs=Table[Coefficient[applied,q[nn+k]],{k,0,ordG}];
D0=Max[Exponent[coeffs,nn]];
log["degree=",ToString[D0]];
charpoly=Sum[Coefficient[coeffs[[k+1]],nn,D0]*lam^k,{k,0,ordG}];
log["charpoly(lead): ",ToString[InputForm[charpoly]]];
Do[log["COEF c_",ToString[k],"(n) = ",ToString[InputForm[coeffs[[k+1]]]]],{k,0,ordG}];
log["DONE ",DateString[]]; Close[lf]; Exit[];
