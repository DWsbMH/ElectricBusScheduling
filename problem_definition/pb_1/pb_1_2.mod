set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

param nJarat;
set Jaratok := 1 .. nJarat;
param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc

param nBusz;
set Buszok := 1..nBusz;

param maxjarat:=5;
set Hanyadik := 1..maxjarat;

var hozzarendel{Buszok,Hanyadik,Jaratok}, binary;
var koztesutazik{Buszok, h in Hanyadik:h!=maxjarat} >=0;


s.t. egybuszegyszerremax1 {b in Buszok, h in Hanyadik} : sum {j in Jaratok} hozzarendel[b,h,j]<=1;

#minden járat el legyen végezve
s.t. mindenJaratElvegezve {j in Jaratok} : sum {b in Buszok, h in Hanyadik} hozzarendel[b,h,j]=1;

s.t. jaratokegymasmellett{b in Buszok, h in Hanyadik: h!=maxjarat}:
  sum{j in Jaratok}hozzarendel[b,h,j] >= sum{j in Jaratok}hozzarendel[b,h+1,j];

s.t. idokorlat{b in Buszok, h in Hanyadik, j in Jaratok, j2 in Jaratok: h!=maxjarat}:
  mikortol[j2] >= (meddig[j]+ido[hova[j],honnan[j2]]) * (-1+hozzarendel[b,h,j]+hozzarendel[b,h+1,j2]);

s.t. koztesutazikbeallito{b in Buszok, h in Hanyadik, j in Jaratok, j2 in Jaratok:h!=maxjarat}:
  koztesutazik[b,h]>=tav[hova[j],honnan[j2]]*(-1+hozzarendel[b,h,j]+hozzarendel[b,h+1,j2]);

s.t. koztesutazikbeallito2{b in Buszok, h in Hanyadik, j in Jaratok:h!=maxjarat}:
  koztesutazik[b,h]>=(sum {j2 in Jaratok} tav[hova[j],honnan[j2]]*hozzarendel[b,h+1,j2])
                    - (max{j2 in Jaratok} tav[hova[j],honnan[j2]])*(1-hozzarendel[b,h,j]);

s.t. koztesutazikbeallito3{b in Buszok, h in Hanyadik, j2 in Jaratok:h!=maxjarat}:
  koztesutazik[b,h]>=(sum {j in Jaratok} tav[hova[j],honnan[j2]]*hozzarendel[b,h,j])
                    - (max{j in Jaratok} tav[hova[j],honnan[j2]])*(1-hozzarendel[b,h+1,j2]);

minimize Koztestav:
  sum{b in Buszok, h in Hanyadik: h!=maxjarat}
    koztesutazik[b,h];
    
solve;

printf "Osszes tavolsag: %g\n", Koztestav;

for{b in Buszok}
{
  printf "Busz %d:\n",b;
  for{h in Hanyadik: sum{j in Jaratok} hozzarendel[b,h,j]=1}
  {
    for{j in Jaratok: hozzarendel[b,h,j]=1}
    {
      printf "\t 1. jarat: Jarat-%d: %s(%g) -> %s(%g)\n",j,honnan[j],mikortol[j],hova[j],meddig[j];
      for{{0}:h!=maxjarat}
      {
        printf "\t\t Atmenes: %g\n",koztesutazik[b,h];
      }
    }
  }
  
}
end;
