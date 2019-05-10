set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

set Jaratok;
set Toltojaratok;

param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc
param tav2 {Jaratok}; #valodi tavolsag a jarat 2 vegpontja kozott

#azok a járatpárok amik nem mehetnek egy busszal
set kulonbozobusz := setof{j in Jaratok, j2 in Jaratok: mikortol[j]<=mikortol[j2] && mikortol[j2]<meddig[j]+ido[hova[j],honnan[j2]] && j!=j2} (j,j2);

set Toltohelyek;

param TH := max {j in Jaratok} meddig[j];
param toltes_slot;

set Toltojaratok := setof {t in Toltohelyek, s in 1..(TH/toltes_slot)}
 t & '_' & s;


set MindenJarat := Jaratok union Toltojaratok;

# fuggvenyeket ide hol, slot

param nBusz;
set Buszok := 1..nBusz;

param depo{Buszok} symbolic, in Helyek;

param maxtoltes{Buszok}; # Watt

param M:=10000;

param fogyasztas{Buszok}; #a buszok kilometerenkenti energiafogyasztasa (watt/km)

var hozzarendel{MindenJarat,Buszok}, binary; # itt sok helyen JAratok -> Mindenjarat
var atmegy{Buszok,Jaratok,Jaratok}, binary;

#az adott járat az elso/utolsó-e annak a busznak
var elsojarate{Jaratok,Buszok}, binary;
var utolsojarate{Jaratok,Buszok}, binary;

var osszhasznalat{Buszok}>=0; #km
var osszfogyasztas{Buszok}>=0; #toltes

#a busz toltottsege az adott jarat elott es utan
var toltottsege{j in Jaratok,b in Buszok}>=0,<=maxtoltes[b];
var toltottsegu{j in Jaratok,b in Buszok}>=0,<=maxtoltes[b];


#minden járat el legyen végezve
s.t. mindenJaratElvegezve1 {j in Jaratok} : sum {b in Buszok} hozzarendel[j,b]=1;

# ugyanigy Jaratok diff Toltojaratok -----> Jaratok
# JAratok -> MindenJarat

s.t. mindenJaratElvegezve2 {j2 in Toltojaratok} : sum {b in Buszok} hozzarendel[j2,b]<=1;

#ha nem az elso járata a busznak, akkor csak olyan járatot vállalhat ahol a következo járat kezdési ideje - az aktuális járat vége között van e elégido hogy átjusson
s.t. OsszeferhetetlenJaratok{(j,j2) in kulonbozobusz, b in Buszok}:
  hozzarendel[j,b]+hozzarendel[j2,b]<=1;

#atmegy 1 lesz ha mindkettohöz hozzá van rendelve é nincs köztes
s.t. Atmegyconstraint{b in Buszok, j in Jaratok, j2 in Jaratok:mikortol[j2]>meddig[j] }:
  atmegy[b,j,j2]
  + sum {jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]} hozzarendel[jkoztes,b]
  >=-1+hozzarendel[j,b]+hozzarendel[j2,b];

s.t. Atmegyconstraint_elesito{b in Buszok, j in Jaratok, j2 in Jaratok}:
  atmegy[b,j,j2]<=(hozzarendel[j,b]+hozzarendel[j2,b])/2;
  
s.t. Atmegyconstraint_elesito2{b in Buszok, j in Jaratok, j2 in Jaratok,jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]}:
  atmegy[b,j,j2]<=1-hozzarendel[jkoztes,b];


#Elso jarat constraintek
s.t. CsakAkkorLehetElsoHaHozzarendelt{b in Buszok, j in Jaratok}:
  elsojarate[j,b] <= hozzarendel[j,b];

s.t. LegfeljebbEgyElsojarat{b in Buszok}:
  sum{j in Jaratok} elsojarate[j,b] <= 1;

# redundans a kettovel felettivel de lehet gyorsit
s.t. NincsElsojaratHaNincsHozzarendelveSemmi{b in Buszok}:
  sum{j in Jaratok} elsojarate[j,b] <= sum{j in Jaratok} hozzarendel[j,b];

s.t. KellElsojaratHavanLegalabbEgyHozzarendelve{b in Buszok}:
  sum{j in Jaratok} elsojarate[j,b] >= sum{j in Jaratok} hozzarendel[j,b] / card(Jaratok);

s.t. KesobbiJaratNemLehetElsoHaMarVanKorabbiHozzarendelt
  {b in Buszok, j in Jaratok,j2 in Jaratok: mikortol[j]>mikortol[j2]}:
  elsojarate[j,b] <= 0 + M * (1- hozzarendel[j2,b]);


#Utolso jarat constraintek
s.t. CsakAkkorLehetUtolsoHaHozzarendelt{b in Buszok, j in Jaratok}:
  utolsojarate[j,b] <= hozzarendel[j,b];

s.t. LegfeljebbEgyUtolsojarat{b in Buszok}:
  sum{j in Jaratok} utolsojarate[j,b] <= 1;

# redundans a kettovel felettivel de lehet gyorsit
s.t. NincsUtolsojaratHaNincsHozzarendelveSemmi{b in Buszok}:
  sum{j in Jaratok} utolsojarate[j,b] <= sum{j in Jaratok} hozzarendel[j,b];

s.t. KellUtolsojaratHaVanLegalabbEgyHozzarendelve{b in Buszok}:
  sum{j in Jaratok} utolsojarate[j,b] >= sum{j in Jaratok} hozzarendel[j,b] / card(Jaratok);

s.t. KorabbiJaratNemLehetUtolsoHaMarVanKesobbiHozzarendelt
  {b in Buszok, j in Jaratok,j2 in Jaratok: mikortol[j]<mikortol[j2]}:
  utolsojarate[j,b] <= 0 + M * (1- hozzarendel[j2,b]);


#ha egy busz elvegzi j1 utam a j2 jaratot
s.t. ElotteToltottseg{b in Buszok, j1 in Jaratok, j2 in Jaratok}:
  toltottsege[j2,b]<=toltottsegu[j1,b] -tav[hova[j1],honnan[j2]]*fogyasztas[b]+M*(1-atmegy[b,j1,j2]);


#ha egy b busz elvegzi a j jaratot
s.t. UtanaToltottseg{b in Buszok, j in Jaratok diff Toltojaratok}:
  toltottsegu[j,b]<=toltottsege[j,b]-tav[hova[j],honnan[j]]*fogyasztas[b]+M*(1-hozzarendel[j,b]);


#ha egy b busz elvegzi a tj toltojaratot (feltoltodik maxra)
s.t. UtanaToltottseg2{b in Buszok, tj in Toltojaratok}:
  toltottsegu[tj,b]>=maxtoltes[b]-M*(1-hozzarendel[tj,b]);

#km
s.t. hasznalatkiszamitas {b in Buszok}:
  sum {j1 in Jaratok, j2 in Jaratok} tav[hova[j1],honnan[j2]]*atmegy[b,j1,j2]
  +
  sum {j in Jaratok}elsojarate[j,b]*tav[depo[b],honnan[j]]
  +
  sum {j in Jaratok}utolsojarate[j,b]*tav[hova[j],depo[b]]
  +
  sum {j in Jaratok} hozzarendel[j,b]*tav2[j]
  = osszhasznalat[b];
  

s.t. osszesfogyasztas{b in Buszok}:
  osszfogyasztas[b] = osszhasznalat[b]*fogyasztas[b];

#mikor menjen tolteni?

minimize osszfogyasztas_minden_buszra: sum {b in Buszok} osszfogyasztas[b];

solve;

printf "Osszes fogyasztas: %g\n", sum{b in Buszok} osszfogyasztas[b];


for{b in Buszok}
{
  printf "Busz %d:\n",b;
  printf "Ossz futott km  / toltes: %g / %g \n",osszhasznalat[b],osszfogyasztas[b];
  for{j in Jaratok:hozzarendel[j,b]=1}
    printf "\tJarat %s: %s(%g) --%g--> %s(%g)\n",j,honnan[j],mikortol[j],tav[honnan[j],hova[j]],hova[j],meddig[j];
  for{j in Jaratok: elsojarate[j,b]=1}
    printf "\tElsojarat: Depo --%g--> Jarat %s : %s(%g) -> %s(%g)\n",tav[depo[b],honnan[j]],j,depo[b],0,honnan[j],mikortol[j];
  for{j in Jaratok, j2 in Jaratok: atmegy[b,j,j2]=1}
    printf "\tAtmenes: Jarat %s --%g--> Jarat %s : %s(%g) -> %s(%g)\n",j,tav[hova[j],honnan[j2]],j2,hova[j],meddig[j],honnan[j2],mikortol[j2];
  
}
end;
