set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

param jaratszam;
set Jaratok := 1 .. jaratszam;
param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc

param buszszam;
set Buszok := 1..buszszam;

param maxjarat:=5;
set Sorszam := 1..maxjarat;

var hozzarendel{Buszok,Sorszam,Jaratok}, binary;
var koztesutazas{Buszok, s in Sorszam:s!=maxjarat} >=0; #km

s.t. JaratokElvegzese {j in Jaratok} : sum {b in Buszok, s in Sorszam} hozzarendel[b,s,j]=1;

s.t. EgyHelyreEgyet {b in Buszok, s in Sorszam} : sum {j in Jaratok} hozzarendel[b,s,j]<=1;

s.t. EgymasMellettiJaratok{b in Buszok, s in Sorszam: s!=maxjarat}:
  sum{j in Jaratok}hozzarendel[b,s,j] >= sum{j in Jaratok}hozzarendel[b,s+1,j];

s.t. Idokorlat{b in Buszok, s in Sorszam, j in Jaratok, j2 in Jaratok: s!=maxjarat}:
  mikortol[j2] >= (meddig[j]+ido[hova[j],honnan[j2]]) * (-1+hozzarendel[b,s,j]+hozzarendel[b,s+1,j2]);

s.t. KoztesKmBeallitas1{b in Buszok, s in Sorszam, j in Jaratok, j2 in Jaratok:s!=maxjarat}:
  koztesutazas[b,s]>=tav[hova[j],honnan[j2]]*(-1+hozzarendel[b,s,j]+hozzarendel[b,s+1,j2]);

s.t. KoztesKmBeallitas2{b in Buszok, s in Sorszam, j in Jaratok:s!=maxjarat}:
  koztesutazas[b,s]>=(sum {j2 in Jaratok} tav[hova[j],honnan[j2]]*hozzarendel[b,s+1,j2])
                    - (max{j2 in Jaratok} tav[hova[j],honnan[j2]])*(1-hozzarendel[b,s,j]);

s.t. KoztesKmBeallitas3{b in Buszok, s in Sorszam, j2 in Jaratok:s!=maxjarat}:
  koztesutazas[b,s]>=(sum {j in Jaratok} tav[hova[j],honnan[j2]]*hozzarendel[b,s,j])
                    - (max{j in Jaratok} tav[hova[j],honnan[j2]])*(1-hozzarendel[b,s+1,j2]);

minimize Koztestav:
  sum{b in Buszok, s in Sorszam: s!=maxjarat}
    koztesutazas[b,s];
    
solve;

printf "Osszes tavolsag: %g\n", Koztestav;
for{b in Buszok}
{
  printf "Busz %d:\n",b;
  for{s in Sorszam: sum{j in Jaratok} hozzarendel[b,s,j]=1}
  {
    for{j in Jaratok: hozzarendel[b,s,j]=1}
    {
      printf "\t 1. jarat: Jarat-%d: %s(%g) -> %s(%g)\n",j,honnan[j],mikortol[j],hova[j],meddig[j];
      for{{0}:s!=maxjarat}
      {
        printf "\t\t Atmenes: %g\n",koztesutazas[b,s];
      }
    }
  }
}
end;