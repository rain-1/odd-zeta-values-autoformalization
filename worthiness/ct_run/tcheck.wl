gB[x_,y_]:=Gamma[x]Gamma[y]/Gamma[x+y];
summ[n_,a_,b_,c_,d_,k_,j_]:=Binomial[n+a,a] Binomial[n+b,b] Binomial[n+c,c] Binomial[n+d,d]*
  (-1)^k Binomial[a+b,k] gB[n+1+k,n+1]^2*(-1)^j Binomial[b+c,j] gB[n+j+1,n+1] gB[n+j+1,n+d+1]*
  gB[n+a+b+1,n+1] gB[2 n+2+a+b+c+d,n+1] gB[n+b+c+d+1,n+1];
ts={{1,0,0,0,0,0,0},{1,1,0,0,0,0,0},{1,1,1,0,0,1,0},{2,1,1,1,1,1,1},{1,2,1,0,0,2,1},{3,0,1,2,1,0,1}};
Do[Print[t," ",InputForm[summ@@t]],{t,ts}];
Exit[];
