set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

param jaratszam;
set Jaratok := 1 .. jaratszam;
param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc

set Kulonbozobusz := setof{j in Jaratok, j2 in Jaratok: mikortol[j]<=mikortol[j2] && mikortol[j2]<meddig[j]+ido[hova[j],honnan[j2]] && j!=j2} (j,j2);

param buszszam;
set Buszok := 1..buszszam;

var hozzarendel{Jaratok,Buszok}, binary;
var atmenet{Buszok,Jaratok,Jaratok}, binary;

s.t. JaratokElvegzese {j in Jaratok} : sum {b in Buszok} hozzarendel[j,b]=1;

s.t. OsszeferhetetlenJaratok{(j,j2) in Kulonbozobusz, b in Buszok}:
  hozzarendel[j,b]+hozzarendel[j2,b]<=1;

s.t. AtmenetKorlatozas{b in Buszok, j in Jaratok, j2 in Jaratok:mikortol[j2]>=meddig[j] }:
  atmenet[b,j,j2]
  + sum {jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]} hozzarendel[jkoztes,b]
  >=-1+hozzarendel[j,b]+hozzarendel[j2,b];

s.t. AtmenetKorlatozas_elesito1{b in Buszok, j in Jaratok, j2 in Jaratok}:
  atmenet[b,j,j2]<=(hozzarendel[j,b]+hozzarendel[j2,b])/2;
  
s.t. AtmenetKorlatozas_elesito2
  {b in Buszok, j in Jaratok, j2 in Jaratok,jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]}:
  atmenet[b,j,j2]<=1-hozzarendel[jkoztes,b];

minimize Koztestav: sum {b in Buszok, j1 in Jaratok, j2 in Jaratok} tav[hova[j1],honnan[j2]]*atmenet[b,j1,j2];

solve;

printf "Osszes tavolsag: %g\n", Koztestav;

for{b in Buszok}
{
  printf "Busz %d:\n",b;
  for{j in Jaratok:hozzarendel[j,b]=1}
    printf "\tJarat %d: %s(%g) -> %s(%g)\n",j,honnan[j],mikortol[j],hova[j],meddig[j];
  for{j in Jaratok, j2 in Jaratok: atmenet[b,j,j2]=1}
    printf "\tAtmenes: Jarat %d --%g--> Jarat %d : %s(%g) -> %s(%g)\n",j,tav[hova[j],honnan[j2]],j2,hova[j],meddig[j],honnan[j2],mikortol[j2];
  
}
end;