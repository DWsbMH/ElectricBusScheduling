set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

param nJarat;
set Jaratok := 1 .. nJarat;
param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc

set kulonbozobusz := setof{j in Jaratok, j2 in Jaratok: mikortol[j]<=mikortol[j2] && mikortol[j2]<meddig[j]+ido[hova[j],honnan[j2]] && j!=j2} (j,j2);

param nBusz;
set Buszok := 1..nBusz;


var hozzarendel{Jaratok,Buszok}, binary;
var atmegy{Buszok,Jaratok,Jaratok}, binary;

#minden busz maximum 5 j�ratot v�llalhat
s.t. mindenBuszMaximumOtJaratot {b in Buszok} : sum {j in Jaratok} hozzarendel[j,b]<=5;

#minden j�rat el legyen v�gezve
s.t. mindenJaratElvegezve {j in Jaratok} : sum {b in Buszok} hozzarendel[j,b]=1;


#ha nem az els� j�rata a busznak, akkor csak olyan j�ratot v�llalhat ahol a k�vetkez� j�rat kezd�si ideje - az aktu�lis j�rat v�ge k�z�tt van e el�gid� hogy �tjusson
s.t. OsszeferhetetlenJaratok{(j,j2) in kulonbozobusz, b in Buszok}:
  hozzarendel[j,b]+hozzarendel[j2,b]<=1;

s.t. Atmegyconstraint{b in Buszok, j in Jaratok, j2 in Jaratok:mikortol[j2]>meddig[j] }:
  atmegy[b,j,j2]
  + sum {jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]} hozzarendel[jkoztes,b]
  >=-1+hozzarendel[j,b]+hozzarendel[j2,b];

s.t. Atmegyconstraint_elesito{b in Buszok, j in Jaratok, j2 in Jaratok}:
  atmegy[b,j,j2]<=(hozzarendel[j,b]+hozzarendel[j2,b])/2;
  
s.t. Atmegyconstraint_elesito2{b in Buszok, j in Jaratok, j2 in Jaratok,jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]}:
  atmegy[b,j,j2]<=1-hozzarendel[jkoztes,b];

  
#cel a koztes km-ek minimalizalasa-minim�lis legyen az �tjut�si km : minden buszra a j�ratain�l az utols� helyt�l a k�vetkez� helyig l�v� t�vols�gok �sszege
minimize Koztestav: sum {b in Buszok, j1 in Jaratok, j2 in Jaratok} tav[hova[j1],honnan[j2]]*atmegy[b,j1,j2];

solve;

printf "Osszes tavolsag: %g\n", Koztestav;

for{b in Buszok}
{
  printf "Busz %d:\n",b;
  for{j in Jaratok:hozzarendel[j,b]=1}
    printf "\tJarat %d: %s(%g) -> %s(%g)\n",j,honnan[j],mikortol[j],hova[j],meddig[j];
  for{j in Jaratok, j2 in Jaratok: atmegy[b,j,j2]=1}
    printf "\tAtmenes: Jarat %d --%g--> Jarat %d : %s(%g) -> %s(%g)\n",j,tav[hova[j],honnan[j2]],j2,hova[j],meddig[j],honnan[j2],mikortol[j2];
  
}
end;
