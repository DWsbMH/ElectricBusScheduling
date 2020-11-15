set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

set Jaratok;
set Toltojaratok;
param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc
param tav2 {Jaratok}; #km
set Kulonbozobusz := setof{j in Jaratok, j2 in Jaratok: mikortol[j]<=mikortol[j2] && mikortol[j2]<meddig[j]+ido[hova[j],honnan[j2]] && j!=j2} (j,j2);

param buszszam;
set Buszok := 1..buszszam;
param depo{Buszok} symbolic, in Helyek;
param maxtoltes{Buszok}; # Watt
param fogyasztas{Buszok}; #Watt/km

param M:=10000;

var hozzarendel{Jaratok,Buszok}, binary;
var atmenet{Buszok,Jaratok,Jaratok}, binary;

var elsojarat{Jaratok,Buszok}, binary;
var utolsojarat{Jaratok,Buszok}, binary;

var osszhasznalat{Buszok}>=0; #km
var osszfogyasztas{Buszok}>=0; #Watt

var toltottsege{j in Jaratok,b in Buszok}>=0,<=maxtoltes[b];
var toltottsegu{j in Jaratok,b in Buszok}>=0,<=maxtoltes[b];

s.t. JaratokElvegzese1 {j in (Jaratok diff Toltojaratok)} : sum {b in Buszok} hozzarendel[j,b]=1;

s.t. JaratokElvegzese2 {j2 in Toltojaratok} : sum {b in Buszok} hozzarendel[j2,b]<=1;

s.t. OsszeferhetetlenJaratok{(j,j2) in Kulonbozobusz, b in Buszok}:
  hozzarendel[j,b]+hozzarendel[j2,b]<=1;

s.t. AtmenetKorlatozas{b in Buszok, j in Jaratok, j2 in Jaratok:mikortol[j2]>meddig[j] }:
  atmenet[b,j,j2]
  + sum {jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]} hozzarendel[jkoztes,b]
  >=-1+hozzarendel[j,b]+hozzarendel[j2,b];

s.t. AtmenetKorlatozas_elesito1{b in Buszok, j in Jaratok, j2 in Jaratok}:
  atmenet[b,j,j2]<=(hozzarendel[j,b]+hozzarendel[j2,b])/2;
  
s.t. AtmenetKorlatozas_elesito2{b in Buszok, j in Jaratok, j2 in Jaratok,jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]}:
  atmenet[b,j,j2]<=1-hozzarendel[jkoztes,b];

#Elso jarat korlatozasok
s.t. ElsoHozzarendeles{b in Buszok, j in Jaratok}:
  elsojarat[j,b] <= hozzarendel[j,b];

# redundans de lehet gyorsit
s.t. ElsoHozzarendeles2{b in Buszok}:
  sum{j in Jaratok} elsojarat[j,b] <= sum{j in Jaratok} hozzarendel[j,b];

s.t. LegfeljebbEgyElso{b in Buszok}:
  sum{j in Jaratok} elsojarat[j,b] <= 1;

s.t. SzuksegesElso{b in Buszok}:
  sum{j in Jaratok} elsojarat[j,b] >= sum{j in Jaratok} hozzarendel[j,b] / card(Jaratok);

s.t. KesobbiNemElso{b in Buszok, j in Jaratok,j2 in Jaratok: mikortol[j]>mikortol[j2]}:
  elsojarat[j,b] <= 0 + M * (1- hozzarendel[j2,b]);

#Utolso jarat korlatozasok
s.t. UtolsoHozzarendeles{b in Buszok, j in Jaratok}:
  utolsojarat[j,b] <= hozzarendel[j,b];

# redundans de lehet gyorsit
s.t. UtolsoHozzarendeles2{b in Buszok}:
  sum{j in Jaratok} utolsojarat[j,b] <= sum{j in Jaratok} hozzarendel[j,b];

s.t. LegfeljebbEgyUtolso{b in Buszok}:
  sum{j in Jaratok} utolsojarat[j,b] <= 1;

s.t. SzuksegesUtolso{b in Buszok}:
  sum{j in Jaratok} utolsojarat[j,b] >= sum{j in Jaratok} hozzarendel[j,b] / card(Jaratok);

s.t. KorabbiNemUtolso{b in Buszok, j in Jaratok,j2 in Jaratok: mikortol[j]<mikortol[j2]}:
  utolsojarat[j,b] <= 0 + M * (1- hozzarendel[j2,b]);

#Toltottsegi szint korlatozasok
s.t. JaratElottiToltottseg{b in Buszok, j1 in Jaratok, j2 in Jaratok}:
  toltottsege[j2,b]<=toltottsegu[j1,b] -tav[hova[j1],honnan[j2]]*fogyasztas[b]+M*(1-atmenet[b,j1,j2]);

s.t. JaratUtaniToltottseg1{b in Buszok, j in Jaratok diff Toltojaratok}:
  toltottsegu[j,b]<=toltottsege[j,b]-tav[hova[j],honnan[j]]*fogyasztas[b]+M*(1-hozzarendel[j,b]);

s.t. JaratUtaniToltottseg2{b in Buszok, tj in Toltojaratok}:
  toltottsegu[tj,b]>=maxtoltes[b]-M*(1-hozzarendel[tj,b]);
  
s.t. OsszhasznalatKiszamitas {b in Buszok}:
  sum {j1 in Jaratok, j2 in Jaratok} tav[hova[j1],honnan[j2]]*atmenet[b,j1,j2]
  +
  sum {j in Jaratok}elsojarat[j,b]*tav[depo[b],honnan[j]]
  +
  sum {j in Jaratok}utolsojarat[j,b]*tav[hova[j],depo[b]]
  +
  sum {j in Jaratok} hozzarendel[j,b]*tav2[j]
  = osszhasznalat[b];

s.t. FogyasztasKiszamitas{b in Buszok}:
  osszfogyasztas[b] = osszhasznalat[b]*fogyasztas[b];

minimize Buszok_osszes_fogyasztasa: sum {b in Buszok} osszfogyasztas[b];

solve;

printf "Osszes fogyasztas: %g\n", sum{b in Buszok} osszfogyasztas[b];

for{b in Buszok}
{
  printf "Busz %d:\n",b;
  printf "Ossz futott km  / Osszfogyasztas / maxtoltes: %g / %g / %g\n",osszhasznalat[b],osszfogyasztas[b],maxtoltes[b];
  for{j in Jaratok:hozzarendel[j,b]=1}
    printf "\tJarat %s: %s(%g) --%g--> %s(%g) (%g)->(%g)\n",j,honnan[j],mikortol[j],tav[honnan[j],hova[j]],hova[j],meddig[j],toltottsege[j,b],toltottsegu[j,b];
  for{j in Jaratok: elsojarat[j,b]=1}
    printf "\tElsojarat: Depo --%g--> Jarat %s : %s(%g) -> %s(%g) (%g)->(%g)\n",tav[depo[b],honnan[j]],j,depo[b],0,honnan[j],mikortol[j],toltottsege[j,b],toltottsegu[j,b];
  for{j in Jaratok, j2 in Jaratok: atmenet[b,j,j2]=1}
    printf "\tAtmenes: Jarat %s --%g--> Jarat %s : %s(%g) -> %s(%g) (%g)->(%g)\n",j,tav[hova[j],honnan[j2]],j2,hova[j],meddig[j],honnan[j2],mikortol[j2],toltottsege[j,b],toltottsegu[j,b];
  for{j in Jaratok: utolsojarat[j,b]=1}
    printf "\tUtolsojarat: Jarat %s --%g--> Depo : %s(%g) -> %s(%g) (%g)->(%g)\n",j,tav[hova[j],depo[b]],hova[j],meddig[j],depo[b],meddig[j]+ido[hova[j],depo[b]],toltottsege[j,b],toltottsegu[j,b];
}

end;