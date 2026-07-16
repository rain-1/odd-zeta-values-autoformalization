(* HyperInt-style iterated integration of the J-form for general n.
   I_n = int_{[0,1]^7} y4^{2n+1} prod_{i!=4} y_i^n prod (1-y_i)^n / (P2 P3 P4 P5)^{n+1} dy
   Usage: set NN (the n value) then run. Integrates y4 first (central), then the rest. *)
nn = NN;  (* set externally, e.g. via -e or edit *)
$Assumptions = And@@(0<#<1&/@{y1,y2,y3,y4,y5,y6,y7});
P2=1-y3 y4(1-y1 y2); P3=1-y3 y4 y5(1-y1 y2)(1-y6 y7); P4=1-y4 y5(1-y6 y7); P5=1-y4 y5(1-y7);
meas = y4^(2 nn+1) y1^nn y2^nn y3^nn y5^nn y6^nn y7^nn *
       ((1-y1)(1-y2)(1-y3)(1-y4)(1-y5)(1-y6)(1-y7))^nn;
expr = meas/(P2 P3 P4 P5)^(nn+1);
order={y4,y1,y2,y6,y7,y3,y5};
Do[v=order[[i]]; t0=AbsoluteTime[];
   r=TimeConstrained[Integrate[expr,{v,0,1}],600,$Aborted];
   If[r===$Aborted,Print["ABORT step ",i," var=",v," (>600s)"];Quit[]];
   expr=Together[r];
   Print["STEP ",i," ",v," leaf=",LeafCount[expr]," t=",Round[AbsoluteTime[]-t0],"s"]; ,
{i,7}];
Print["RESULT n=",nn," : ",N[expr,40]];
(* PSLQ against the weight-<=7 basis to recover exact form *)
basis={1,Zeta[2],Zeta[3],Zeta[5],Zeta[7],Zeta[2]Zeta[3],Zeta[2]Zeta[5]};
val=N[expr,300];
rel=FindIntegerNullVector[Prepend[N[basis,300],-val]];
Print["PSLQ relation (coeff of -val, then basis): ",rel];
