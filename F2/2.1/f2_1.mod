set Products; #term�kek
set Units; #gy�rt�egys�gek
param M:=1000; #"bazi nagy sz�m : Big M"

param steps{Products}; #term�k el��ll�t�s�hoz sz�ks�ges l�p�sek pl A-hoz 3 l�p�s, B-hez 4 l�p�s

set Tasks := setof{p in Products, n in 1..steps[p]}(p,n); #feladatok halmaza az egyes term�kek legy�rt�s�hoz pl (A,1) (A,2) (A,3) ... (D,3)

set Applicable := setof{(p,n) in Tasks, u in Units}(p,n,u);

param proctime {p in Products, n in 1..steps[p], u in Units};

var stime {Tasks}>=0; #adott task kezdete 
var ctime {Tasks}>=0; #adott task v�ge

var choose {Applicable} binary; # pl ha A1es taskot az U3 ba v�gzem el akkor choose[(A,1,U3)]=1

set Precedence := setof {(p,n) in Tasks,(p2,n2) in Tasks: (p!=p2 || n!=n2)} (p,n,p2,n2);

var X {Precedence} binary; #ki kit el�z meg

var makespan >=0; #teljes �tfut�si id�

s.t. ProctimeConstraint {(p,n) in Tasks}:
ctime[p,n] >= stime[p,n] + sum{u in Units} choose[p,n,u] * proctime[p,n,u];

s.t. SubsequentTask {(p,n) in Tasks:n!=1}:
	stime[p,n] >= ctime [p,n-1];
#az el�z� task befejez�se ut�n kezd�dhet a k�vetkez� task A1 ut�n j�n A2

s.t. Sequencing{(p,n,p2,n2) in Precedence, u in Units}:
	stime[p2,n2] >= ctime[p,n] - M *(3-X[p,n,p2,n2]-choose[p,n,u]-choose[p2,n2,u]);
#stime[p2,n2] >= ctime[p,n] ha X[p,n,p2,n2] == 1 �s ugyanabban a Unitban vannak choose[p,n,u]==1 �s choose[p2,n2,u]==1 

s.t. Orderaround{(p,n,p2,n2) in Precedence, u in Units}:
	X[p,n,p2,n2]+X[p2,n2,p,n] >= -1 + choose[p,n,u] + choose[p2,n2,u];
# X[p,n,p2,n2]+X[p2,n2,p,n] >= 1 - M *(2-choose[p,n,u]-choose[p2,n2,u])
# X[p,n,p2,n2]+X[p2,n2,p,n]=1 ha ugyanabban a Unitban vannak choose[p,n,u]==1 �s choose[p2,n2,u]==1 
# A1U1+A1U2+A1U3+A1U4=1
s.t. egyTaskotegyUnitba{(p,n) in Tasks}:
	sum{u in Units} choose[p,n,u]=1;
#(p,n,u) in Applicable,u2,u3,u4 in Units : u!=u2!=u3!=u4  ->>>>> choose[p,n,u]+choose[p,n,u2]+choose[p,n,u3]+choose[p,n,u4]=1;

s.t. Makespanconstraint{(p,n) in Tasks}:
	makespan >= ctime[p,n];

minimize Makespan : makespan;
solve;
for{u in Units}
{
	printf "%s: ",u;
	for{(p,n) in Tasks : choose[p,n,u]==1}
	{
		printf"%s%d[%g-%g] ",p,n,stime[p,n],ctime[p,n];
	}
	printf"\n";
}
end;