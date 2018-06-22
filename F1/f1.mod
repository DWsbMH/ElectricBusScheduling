set Products; #term�kek
set Units; #gy�rt�egys�gek
param M:=1000; #"bazi nagy sz�m : Big M"

param steps{Products}; #term�k el��ll�t�s�hoz sz�ks�ges l�p�sek pl A-hoz 3 l�p�s, B-hez 4 l�p�s

set Tasks := setof{p in Products, n in 1..steps[p]}(p,n); #feladatok halmaza az egyes term�kek legy�rt�s�hoz pl (A,1) (A,2) (A,3) ... (D,3)

param appliable {Tasks},symbolic,within Units; #az egyes feladatokat melyik gy�rt�si egys�g v�gzi el pl A1-et az U1
param proctime {Tasks}; # az egyes feladatok v�grehajt�s�nak ideje �r�ban pl A1-nek 15 �ra

var stime {Tasks}>=0; #adott task kezdete 
var ctime {Tasks}>=0; #adott task v�ge

set Precedence := setof {(p,n) in Tasks,(p2,n2) in Tasks: (p!=p2 || n!=n2) && appliable[p,n]==appliable[p2,n2]} (p,n,p2,n2);
#p�ronk�nt az ugyanabban az egys�gben lev� feladatok halmaza

var X {Precedence} binary; #ki kit el�z meg
# X[p,n,p2,n2] = 1  ha pn megelozi p2n2-t

var makespan >=0; #teljes �tfut�si id�

s.t. ProctimeConstraint {(p,n) in Tasks}:
ctime[p,n] >= stime[p,n] + proctime[p,n];
#  ctime[p,n] >= stime[p,n] + sum{u in J[p,n]} y[p,n,u] * proctime[p,n,u]

s.t. SubsequentTask {(p,n) in Tasks:n!=1}:
	stime[p,n] >= ctime [p,n-1];
#az el�z� task befejez�se ut�n kezd�dhet a k�vetkez� task

s.t. Sequencing{(p,n,p2,n2) in Precedence}:
	#stime[p2,n2] >= ctime[p,n] ha X[p,n,p2,n2] == 1;
	stime[p2,n2] >= ctime[p,n] - M *(1-X[p,n,p2,n2]);

s.t. Orderaround{(p,n,p2,n2) in Precedence}:
	X[p,n,p2,n2]+X[p2,n2,p,n]=1;
	
s.t. Makespanconstraint{(p,n) in Tasks}:
	makespan >= ctime[p,n];
	
#sorrend a taskokban mi mi ut�n j�het --> csak A1 ut�n j�het A2

#csak azut�n ind�thatok egy m�sik taskot az adott unitban ha az el�z� task v�get�rt

#a storage unlimited -> ide rakhatom "pihenni" a taskokat ha �pp v�rakoznak egy unitra


#min�l hamarabb befejezz�k az �sszes feladatot ->az utols� task v�ge legyen min�l hamarabb
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

#form�tum p�lda:
/*
U1: (B 1) (A 1) (C 2)
U2: (B 2) (C 2) (D 3)
U3: (C 1) (D 2) (A 2) (B 3)
U4: (D 1) (A 3) (B 4)
*/