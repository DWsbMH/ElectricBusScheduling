set J ;
set TH;

set Jcs := setof {th in TH, s in 1..8} "charge_at_" & th & "_from_" & 2*(s-1) & "_until_" & 2*s;

set Jmind := J union Jcs;

minimize foo: 0;

solve;

printf "Jcs: ";
for {j in Jcs} printf "\t%s\n",j;

printf "\n\n";


printf "Jmind: ";
for {j in Jmind} printf "\t%s\n",j;

printf "\n\n";

data;

set J := j1 j2 j3;
set TH := t1 t2;
