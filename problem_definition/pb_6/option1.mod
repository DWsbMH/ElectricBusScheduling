set ize;
set th;
set bize:= setof {h in th, t in 1..12} h & '_'&t;
param _hely{b in bize} := substr(b,1,1);
param _slot{b in bize} := substr(b,3);

set minden := ize union bize;


param mettol{m in minden}, default (_slot[m]-1)*180;

minimize z:0;

solve;

for {i in minden}
  printf "%s - %g\n",i,mettol[i];

data;

set ize := A B;

set th :=  w e;

param mettol:=
A 1
B 2
;
