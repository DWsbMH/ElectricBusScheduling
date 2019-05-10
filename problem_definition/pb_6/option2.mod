set ize;
set th;
set bize:= setof {h in th, t in 1..12} h & '_'&t;
param _hely{b in bize} := substr(b,1,1);
param _slot{b in bize} := substr(b,3);

set minden := ize union bize;

param mettol_ize{ize};
param mettol_bize {b in bize}:= (_slot[b]-1)*10;

param mettol{m in minden} := if m in ize then mettol_ize[m]
                        else mettol_bize[m];

minimize z:0;

solve;

for {i in minden}
  printf "%s - %g\n",i,mettol[i];

data;

set ize := A B;

set th :=  w e;

param mettol_ize:=
A 1
B 2
;
