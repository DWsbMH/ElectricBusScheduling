set Products; #termékek
set Units; #gyártóegységek
param M:=1000; #"bazi nagy szám : Big M"

param steps{Products}; #termék elõállításához szükséges lépések pl A-hoz 3 lépés, B-hez 4 lépés

set Tasks := setof{p in Products, n in 1..steps[p]}(p,n); #feladatok halmaza az egyes termékek legyártásához pl (A,1) (A,2) (A,3) ... (D,3)

param appliable {Tasks},symbolic,within Units; #az egyes feladatokat melyik gyártási egység végzi el pl A1-et az U1
param proctime {Tasks}; # az egyes feladatok végrehajtásának ideje órában pl A1-nek 15 óra

var stime {Tasks}>=0; #adott task kezdete 
var ctime {Tasks}>=0; #adott task vége

set Precedence := setof {(p,n) in Tasks,(p2,n2) in Tasks: (p!=p2 || n!=n2) && appliable[p,n]==appliable[p2,n2]} (p,n,p2,n2);
#páronként az ugyanabban az egységben levõ feladatok halmaza

var X {Precedence} binary; #ki kit elõz meg
# X[p,n,p2,n2] = 1  ha pn megelozi p2n2-t

var makespan >=0; #teljes átfutási idõ

s.t. ProctimeConstraint {(p,n) in Tasks}:
ctime[p,n] >= stime[p,n] + proctime[p,n];
#  ctime[p,n] >= stime[p,n] + sum{u in J[p,n]} y[p,n,u] * proctime[p,n,u]

s.t. SubsequentTask {(p,n) in Tasks:n!=1}:
	stime[p,n] >= ctime [p,n-1];
#az elõzõ task befejezése után kezdõdhet a következõ task

s.t. Sequencing{(p,n,p2,n2) in Precedence}:
	#stime[p2,n2] >= ctime[p,n] ha X[p,n,p2,n2] == 1;
	stime[p2,n2] >= ctime[p,n] - M *(1-X[p,n,p2,n2]);

s.t. Orderaround{(p,n,p2,n2) in Precedence}:
	X[p,n,p2,n2]+X[p2,n2,p,n]=1;
	
s.t. Makespanconstraint{(p,n) in Tasks}:
	makespan >= ctime[p,n];
	
#sorrend a taskokban mi mi után jöhet --> csak A1 után jöhet A2

#csak azután indíthatok egy másik taskot az adott unitban ha az elõzõ task végetért

#a storage unlimited -> ide rakhatom "pihenni" a taskokat ha épp várakoznak egy unitra


#minél hamarabb befejezzük az összes feladatot ->az utolsó task vége legyen minél hamarabb
minimize Makespan : makespan;

solve;
for{u in Units}
{
	printf "%s: ",u;
	for{(p,n) in Tasks : appliable[p,n]==u}
	{
		printf"%s%d[%g-%g] ",p,n,stime[p,n],ctime[p,n];
	}
	printf"\n";
}
end;

#formátum példa:
/*
U1: (B 1) (A 1) (C 2)
U2: (B 2) (C 2) (D 3)
U3: (C 1) (D 2) (A 2) (B 3)
U4: (D 1) (A 3) (B 4)
*/