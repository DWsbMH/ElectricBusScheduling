set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

set MindenJarat;
set Toltojaratok;
param honnan{MindenJarat} symbolic, in Helyek;
param hova{MindenJarat} symbolic, in Helyek;
param mikortol{MindenJarat}; #perc
param meddig{MindenJarat}; #perc
param tav2 {MindenJarat}; #km
set Kulonbozobusz := setof{j in MindenJarat, j2 in MindenJarat: mikortol[j]<=mikortol[j2] && mikortol[j2]<meddig[j]+ido[hova[j],honnan[j2]] && j!=j2} (j,j2);

param buszszam;
set Buszok := 1..buszszam;
param depo{Buszok} symbolic, in Helyek;
param maxtoltes{Buszok}; # Watt
param fogyasztas{Buszok}; #Watt/km

param M:=10000;

var hozzarendel{MindenJarat,Buszok}, binary;
var atmenet{Buszok,MindenJarat,MindenJarat}, binary;

var elsojarat{MindenJarat,Buszok}, binary;
var utolsojarat{MindenJarat,Buszok}, binary;

var osszhasznalat{Buszok}>=0; #km
var osszfogyasztas{Buszok}>=0; #Watt

var toltottsege{j in MindenJarat,b in Buszok}>=0,<=maxtoltes[b];
var toltottsegu{j in MindenJarat,b in Buszok}>=0,<=maxtoltes[b];

s.t. JaratokElvegzese1 {j in (MindenJarat diff Toltojaratok)} : sum {b in Buszok} hozzarendel[j,b]=1;

s.t. JaratokElvegzese2 {j2 in Toltojaratok} : sum {b in Buszok} hozzarendel[j2,b]<=1;

s.t. OsszeferhetetlenJaratok{(j,j2) in Kulonbozobusz, b in Buszok}:
  hozzarendel[j,b]+hozzarendel[j2,b]<=1;

s.t. AtmenetKorlatozas{b in Buszok, j in MindenJarat, j2 in MindenJarat:mikortol[j2]>=meddig[j] }:
  atmenet[b,j,j2]
  + sum {jkoztes in MindenJarat: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]} hozzarendel[jkoztes,b]
  >=-1+hozzarendel[j,b]+hozzarendel[j2,b];

s.t. AtmenetKorlatozas_elesito1{b in Buszok, j in MindenJarat, j2 in MindenJarat}:
  atmenet[b,j,j2]<=(hozzarendel[j,b]+hozzarendel[j2,b])/2;
  
s.t. AtmenetKorlatozas_elesito2{b in Buszok, j in MindenJarat, j2 in MindenJarat,jkoztes in MindenJarat: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]}:
  atmenet[b,j,j2]<=1-hozzarendel[jkoztes,b];

#Elso jarat korlatozasok
s.t. ElsoHozzarendeles{b in Buszok, j in MindenJarat}:
  elsojarat[j,b] <= hozzarendel[j,b];

# redundans de lehet gyorsit
s.t. ElsoHozzarendeles2{b in Buszok}:
  sum{j in MindenJarat} elsojarat[j,b] <= sum{j in MindenJarat} hozzarendel[j,b];

s.t. LegfeljebbEgyElso{b in Buszok}:
  sum{j in MindenJarat} elsojarat[j,b] <= 1;

s.t. SzuksegesElso{b in Buszok}:
  sum{j in MindenJarat} elsojarat[j,b] >= sum{j in MindenJarat} hozzarendel[j,b] / card(MindenJarat);

s.t. KesobbiNemElso{b in Buszok, j in MindenJarat,j2 in MindenJarat: mikortol[j]>mikortol[j2]}:
  elsojarat[j,b] <=(1- hozzarendel[j2,b]);

#Utolso jarat korlatozasok
s.t. UtolsoHozzarendeles{b in Buszok, j in MindenJarat}:
  utolsojarat[j,b] <= hozzarendel[j,b];

# redundans de lehet gyorsit
s.t. UtolsoHozzarendeles2{b in Buszok}:
  sum{j in MindenJarat} utolsojarat[j,b] <= sum{j in MindenJarat} hozzarendel[j,b];

s.t. LegfeljebbEgyUtolso{b in Buszok}:
  sum{j in MindenJarat} utolsojarat[j,b] <= 1;

s.t. SzuksegesUtolso{b in Buszok}:
  sum{j in MindenJarat} utolsojarat[j,b] >= sum{j in MindenJarat} hozzarendel[j,b] / card(MindenJarat);

s.t. KorabbiNemUtolso{b in Buszok, j in MindenJarat,j2 in MindenJarat: mikortol[j]<mikortol[j2]}:
  utolsojarat[j,b] <=(1- hozzarendel[j2,b]);

#Toltottsegi szint korlatozasok
s.t. DepobolToltottseg{b in Buszok, j in MindenJarat}:
  toltottsege[j,b]<=maxtoltes[b]-tav[depo[b],honnan[j]]*fogyasztas[b]
  +M*(1-elsojarat[j,b]);

s.t. DepobaToltottseg{b in Buszok, j in MindenJarat}:
  toltottsegu[j,b]>=tav[hova[j],depo[b]]*fogyasztas[b]
  -M*(1-utolsojarat[j,b]);

s.t. JaratElottiToltottseg{b in Buszok, j1 in MindenJarat, j2 in MindenJarat}:
  toltottsege[j2,b]<=toltottsegu[j1,b] -tav[hova[j1],honnan[j2]]*fogyasztas[b]+M*(1-atmenet[b,j1,j2]);

s.t. JaratUtaniToltottseg1{b in Buszok, j in MindenJarat diff Toltojaratok}:
  toltottsegu[j,b]<=toltottsege[j,b]-tav2[j]*fogyasztas[b]+M*(1-hozzarendel[j,b]);

s.t. JaratUtaniToltottseg2{b in Buszok, tj in Toltojaratok}:
  toltottsegu[tj,b]>=maxtoltes[b]-M*(1-hozzarendel[tj,b]);
  
s.t. OsszhasznalatKiszamitas {b in Buszok}:
  sum {j1 in MindenJarat, j2 in MindenJarat} tav[hova[j1],honnan[j2]]*atmenet[b,j1,j2]
  +
  sum {j in MindenJarat}elsojarat[j,b]*tav[depo[b],honnan[j]]
  +
  sum {j in MindenJarat}utolsojarat[j,b]*tav[hova[j],depo[b]]
  +
  sum {j in MindenJarat} hozzarendel[j,b]*tav2[j]
  = osszhasznalat[b];

s.t. FogyasztasKiszamitas{b in Buszok}:
  osszfogyasztas[b] = osszhasznalat[b]*fogyasztas[b];

minimize Buszok_osszes_fogyasztasa: sum {b in Buszok} osszfogyasztas[b];

solve;

printf "Osszes fogyasztas: %g\n", sum{b in Buszok} osszfogyasztas[b];
for{b in Buszok}
{
  printf "Busz %d:\n",b;
  printf "Ossz futott km / Osszfogyasztas / maxtoltes: %g / %g / %g\n",osszhasznalat[b],osszfogyasztas[b],maxtoltes[b];
  printf "\tJaratok/Toltesek:\n";
  for{j in MindenJarat:hozzarendel[j,b]=1}
    printf "\t\tJarat %s: %s (%g) --%g--> %s (%g) (%g)->(%g)\n",j,honnan[j],mikortol[j],tav2[j],hova[j],meddig[j],toltottsege[j,b],toltottsegu[j,b];
  
  printf "\tAtmenetek:\n";
  for{j in MindenJarat: elsojarat[j,b]=1}
    printf "\tElsojarat: Depo --%g--> Jarat %s: %s (%g) -> %s (%g) (%g)->(%g)\n",tav[depo[b],honnan[j]],j,depo[b],0,honnan[j],mikortol[j],toltottsege[j,b]+tav[depo[b],honnan[j]]*fogyasztas[b],toltottsege[j,b];
  for{j in MindenJarat, j2 in MindenJarat: atmenet[b,j,j2]=1}
    printf "\tAtmenet: Jarat %s --%g--> Jarat %s: %s (%g) -> %s (%g) (%g)->(%g)\n",j,tav[hova[j],honnan[j2]],j2,hova[j],meddig[j],honnan[j2],mikortol[j2],toltottsegu[j,b],toltottsege[j2,b];
  for{j in MindenJarat: utolsojarat[j,b]=1}
    printf "\tUtolsojarat: Jarat %s --%g--> Depo: %s (%g) -> %s (%g) (%g)->(%g)\n",j,tav[hova[j],depo[b]],
    hova[j],meddig[j],depo[b],meddig[j]+ido[hova[j],depo[b]],toltottsegu[j,b],toltottsegu[j,b]-tav[hova[j],depo[b]]*fogyasztas[b];
}

end;