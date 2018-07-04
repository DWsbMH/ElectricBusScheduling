set Products; #term�kek
set Units; #gy�rt�egys�gek
param M:=1000; #"bazi nagy sz�m : Big M"

param batches{Products};#h�ny darabot �ll�tok el� a term�kb�l
param steps{Products}; #term�k elo�ll�t�s�hoz sz�ks�ges l�p�sek pl A-hoz 3 l�p�s, B-hez 4 l�p�s

set Tasks := setof{p in Products, b in 1..batches[p], n in 1..steps[p]}(p,b,n); 
#feladatok halmaza az egyes term�kek legy�rt�s�hoz pl (A,1,1) (A,1,2) (A,1,3) ... (C,1,3)<-egy term�k h�nyadik batch�nek h�nyadik l�p�se

param proctime {p in Products, n in 1..steps[p], u in Units},default -1;

set Applicable := setof{(p,b,n) in Tasks, u in Units : proctime[p,n,u]!=-1}(p,b,n,u);

var stime {Tasks}>=0; #adott task kezdete 
var ctime {Tasks}>=0; #adott task v�ge

var choose {Applicable} binary; # pl ha (A,1,1)es taskot az U3 ba v�gzem el akkor choose[(A,1,1,U3)]=1

set Conflicts := setof {(p,b,n,u) in Applicable,(p2,b2,n2,u) in Applicable : p!=p2 || b!=b2 || n!=n2} (p,b,n,u,p2,b2,n2); #azok a p�rok amik �tk�zhetnek

set Precedence := setof {(p,b,n,u,p2,b2,n2) in Conflicts} (p,b,n,p2,b2,n2);

var X {Precedence} binary; #ki kit eloz meg

var makespan >=0; #teljes �tfut�si ido

s.t. ProctimeConstraint {(p,b,n) in Tasks}:
ctime[p,b,n] >= stime[p,b,n] + sum{(p,b,n,u) in Applicable} choose[p,b,n,u] * proctime[p,n,u];

#az elozo task befejez�se ut�n kezdodhet a k�vetkezo task A1 ut�n j�n A2
#s.t. SubsequentTask {(p,n) in Tasks:n!=1}:stime[p,n] >= ctime [p,n-1];
# A,1,1 ut�n A,1,2
s.t. SubsequentTask {(p,b,n) in Tasks:n!=1}:
	stime[p,b,n] >= ctime [p,b,n-1];
#A,1,v�ge ut�n A,2,eleje
s.t. SubsequentBatch {(p,b,1) in Tasks :b!=1}:
	stime[p,b,1] >= stime [p,b-1,1];

s.t. Sequencing{(p,b,n,u,p2,b2,n2) in Conflicts}:
	stime[p2,b2,n2] >= ctime[p,b,n] - M *(1-X[p,b,n,p2,b2,n2]);
#stime[p2,n2] >= ctime[p,n] ha X[p,n,p2,n2] == 1 �s ugyanabban a Unitban vannak choose[p,n,u]==1 �s choose[p2,n2,u]==1 

s.t. Orderaround{(p,b,n,u,p2,b2,n2) in Conflicts}:
	X[p,b,n,p2,b2,n2]+X[p2,b2,n2,p,b,n] >= -1 + choose[p,b,n,u] + choose[p2,b2,n2,u];

s.t. egyTaskotegyUnitba{(p,b,n) in Tasks}:
	sum{(p,b,n,u) in Applicable} choose[p,b,n,u]=1;

s.t. Makespanconstraint{(p,b,n) in Tasks : n==steps[p]}:
	makespan >= ctime[p,b,n];

minimize Makespan : makespan;
solve;
for{u in Units}
{
	printf "%s: ",u;
	for{(p,b,n,u) in Applicable : choose[p,b,n,u]==1}
	{
		printf"%s%d%d[%g-%g] ",p,b,n,stime[p,b,n],ctime[p,b,n];
	}
	printf"\n";
}

printf "\n\n";
for{(p,b,n,p2,b2,n2) in Precedence:X[p,b,n,p2,b2,n2]=1}
    printf "Precedence in %s: %d %d vs %s: %d %d\n",p,b,n,p2,b2,n2;
end;
