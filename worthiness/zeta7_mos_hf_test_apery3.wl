AppendTo[$Path, "/home/ubuntu/riscergosum"]; AppendTo[$Path, "/home/ubuntu/riscergosum/RISC"];
Quiet[Get["HolonomicFunctions.m"]];
Print["M06 (Apery zeta3) test start"];
W  = {x1+x2+x3+x4, x3+x4, x2+x3, x1+x2+x3};
xs = {x1,x2,x3,x4};
H = Exp[nn*(Sum[Log[W[[i]]],{i,4}] - Sum[Log[xs[[j]]],{j,4}])]/Product[xs[[j]],{j,4}];
ann = Annihilator[H, Join[{S[nn]}, Der/@xs]]; Print["ann ready ", Length[ann]];
t0=AbsoluteTime[];
tak = Takayama[ann, xs];
Print["M06TAKDONE in ", Round[AbsoluteTime[]-t0], "s"];
Print[tak];
(* apply to q(nn) to display recurrence *)
Print["--- recurrence ---"]; Print[ApplyOreOperator[tak[[1]], q[nn]]];
