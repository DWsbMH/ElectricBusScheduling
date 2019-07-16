set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

set Jaratok;

param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc
param tav2 {Jaratok}; #valodi tavolsag a jarat 2 vegpontja kozott



set Toltohelyek;

param TH := max {j in Jaratok} meddig[j]; #time horizon
param toltes_slot;

set Toltojaratok := setof {t in Toltohelyek, s in 1..(TH/toltes_slot)}
 t & '_' & s;

param _hely{t in Toltojaratok} symbolic := substr(t,1,1);
param _slot{t in Toltojaratok} := substr(t,3);

set MindenJarat := Jaratok union Toltojaratok;




param honnan_tolto {t in Toltojaratok} symbolic:= _hely[t];

param honnan_minden{m in MindenJarat} symbolic := if m in Jaratok then honnan[m]
                        else honnan_tolto[m];


param hova_tolto {t in Toltojaratok} symbolic:= _hely[t];

param hova_minden{m in MindenJarat} symbolic:= if m in Jaratok then hova[m]
                        else hova_tolto[m];


param mikortol_tolto {t in Toltojaratok}:= (_slot[t]-1)*toltes_slot;

param mikortol_minden{m in MindenJarat} := if m in Jaratok then mikortol[m]
                        else mikortol_tolto[m];


param meddig_tolto {t in Toltojaratok}:= (_slot[t])*toltes_slot;

param meddig_minden{m in MindenJarat} := if m in Jaratok then meddig[m]
                        else meddig_tolto[m];


param tav2_tolto {t in Toltojaratok}:= tav[_hely[t],_hely[t]];

param tav2_minden{m in MindenJarat} := if m in Jaratok then tav2[m]
                        else tav2_tolto[m];

#azok a járatpárok amik nem mehetnek egy busszal
set kulonbozobusz := setof{j in MindenJarat, j2 in MindenJarat: mikortol_minden[j]<=mikortol_minden[j2] && mikortol_minden[j2]<meddig_minden[j]+ido[hova_minden[j],honnan_minden[j2]] && j!=j2} (j,j2);

param nBusz;
set Buszok := 1..nBusz;

param depo{Buszok} symbolic, in Helyek;

param maxtoltes{Buszok}; # Watt

param M:=10000;

param fogyasztas{Buszok}; #a buszok kilometerenkenti energiafogyasztasa (watt/km)

var hozzarendel{MindenJarat,Buszok}, binary;
var atmegy{Buszok,MindenJarat,MindenJarat}, binary;

#az adott járat az elso/utolsó-e annak a busznak
var elsojarate{MindenJarat,Buszok}, binary;
var utolsojarate{MindenJarat,Buszok}, binary;

var osszhasznalat{Buszok}>=0; #km
var osszfogyasztas{Buszok}>=0; #toltes

#a busz toltottsege az adott jarat elott es utan
var toltottsege{j in MindenJarat,b in Buszok}>=0,<=maxtoltes[b];
var toltottsegu{j in MindenJarat,b in Buszok}>=0,<=maxtoltes[b];
var tolteselejen{b in Buszok}>=0,<=maxtoltes[b];
var toltesvegen{b in Buszok}>=0,<=maxtoltes[b];


#minden járat el legyen végezve
s.t. mindenJaratElvegezve1 {j in Jaratok} : sum {b in Buszok} hozzarendel[j,b]=1;

s.t. mindenJaratElvegezve2 {j2 in Toltojaratok} : sum {b in Buszok} hozzarendel[j2,b]<=1;

#ha nem az elso járata a busznak, akkor csak olyan járatot vállalhat ahol a következo járat kezdési ideje - az aktuális járat vége között van e elégido hogy átjusson
s.t. OsszeferhetetlenJaratok{(j,j2) in kulonbozobusz, b in Buszok}:
  hozzarendel[j,b]+hozzarendel[j2,b]<=1;

#atmegy 1 lesz ha mindkettohöz hozzá van rendelve és nincs köztes
s.t. Atmegyconstraint{b in Buszok, j in MindenJarat, j2 in MindenJarat:mikortol_minden[j2]>=meddig_minden[j] }:
  atmegy[b,j,j2]
  + sum {jkoztes in MindenJarat: mikortol_minden[jkoztes]>=meddig_minden[j] && meddig_minden[jkoztes] <= mikortol_minden[j2]} hozzarendel[jkoztes,b]
  >=-1+hozzarendel[j,b]+hozzarendel[j2,b];

s.t. Atmegyconstraint_elesito{b in Buszok, j in MindenJarat, j2 in MindenJarat}:
  atmegy[b,j,j2]<=(hozzarendel[j,b]+hozzarendel[j2,b])/2;
  
s.t. Atmegyconstraint_elesito2{b in Buszok, j in MindenJarat, j2 in MindenJarat,jkoztes in MindenJarat: mikortol_minden[jkoztes]>=meddig_minden[j] && meddig_minden[jkoztes] <= mikortol_minden[j2]}:
  atmegy[b,j,j2]<=1-hozzarendel[jkoztes,b];


#Elso jarat constraintek
s.t. CsakAkkorLehetElsoHaHozzarendelt{b in Buszok, j in MindenJarat}:
  elsojarate[j,b] <= hozzarendel[j,b];

s.t. LegfeljebbEgyElsojarat{b in Buszok}:
  sum{j in MindenJarat} elsojarate[j,b] <= 1;

# redundans a kettovel felettivel de lehet gyorsit
s.t. NincsElsojaratHaNincsHozzarendelveSemmi{b in Buszok}:
  sum{j in MindenJarat} elsojarate[j,b] <= sum{j in MindenJarat} hozzarendel[j,b];

s.t. KellElsojaratHavanLegalabbEgyHozzarendelve{b in Buszok}:
  sum{j in MindenJarat} elsojarate[j,b] >= sum{j in MindenJarat} hozzarendel[j,b] / card(MindenJarat);

s.t. KesobbiJaratNemLehetElsoHaMarVanKorabbiHozzarendelt
  {b in Buszok, j in MindenJarat,j2 in MindenJarat: mikortol_minden[j]>mikortol_minden[j2]}:
  elsojarate[j,b] <= 0 + M * (1- hozzarendel[j2,b]);


#Utolso jarat constraintek
s.t. CsakAkkorLehetUtolsoHaHozzarendelt{b in Buszok, j in MindenJarat}:
  utolsojarate[j,b] <= hozzarendel[j,b];

s.t. LegfeljebbEgyUtolsojarat{b in Buszok}:
  sum{j in MindenJarat} utolsojarate[j,b] <= 1;

# redundans a kettovel felettivel de lehet gyorsit
s.t. NincsUtolsojaratHaNincsHozzarendelveSemmi{b in Buszok}:
  sum{j in MindenJarat} utolsojarate[j,b] <= sum{j in MindenJarat} hozzarendel[j,b];

s.t. KellUtolsojaratHaVanLegalabbEgyHozzarendelve{b in Buszok}:
  sum{j in MindenJarat} utolsojarate[j,b] >= sum{j in MindenJarat} hozzarendel[j,b] / card(MindenJarat);

s.t. KorabbiJaratNemLehetUtolsoHaMarVanKesobbiHozzarendelt
  {b in Buszok, j in MindenJarat,j2 in MindenJarat: mikortol_minden[j]<mikortol_minden[j2]}:
  utolsojarate[j,b] <= 0 + M * (1- hozzarendel[j2,b]);


# Depobol erjen oda az elsobe
s.t. DepobolToltottseg{b in Buszok, j in MindenJarat}:
  toltottsege[j,b]<=tolteselejen[b]-tav[depo[b],honnan_minden[j]]*fogyasztas[b]
  +M*(1-elsojarate[j,b]);


# Depoba a vegen erjen oda
s.t. DepobaToltottseg{b in Buszok, j in MindenJarat}:
  toltesvegen[b]<=toltottsegu[j,b]-tav[hova_minden[j],depo[b]]*fogyasztas[b]
  +M*(1-utolsojarate[j,b]);

#ha egy busz elvegzi j1 utam a j2 jaratot
s.t. ElotteToltottseg{b in Buszok, j1 in MindenJarat, j2 in MindenJarat}:
  toltottsege[j2,b]<=toltottsegu[j1,b] -tav[hova_minden[j1],honnan_minden[j2]]*fogyasztas[b]
  +M*(1-atmegy[b,j1,j2]);


#ha egy b busz elvegzi a j jaratot
s.t. UtanaToltottseg{b in Buszok, j in Jaratok}:
  toltottsegu[j,b]<=toltottsege[j,b]-tav2[j]*fogyasztas[b]+M*(1-hozzarendel[j,b]);


#ha egy b busz elvegzi a tj toltojaratot (feltoltodik maxra)
s.t. UtanaToltottseg2{b in Buszok, tj in Toltojaratok}:
  toltottsegu[tj,b]>=maxtoltes[b]-M*(1-hozzarendel[tj,b]);

#km
s.t. hasznalatkiszamitas {b in Buszok}:
  sum {j1 in MindenJarat, j2 in MindenJarat} tav[hova_minden[j1],honnan_minden[j2]]*atmegy[b,j1,j2]
  +
  sum {j in MindenJarat}elsojarate[j,b]*tav[depo[b],honnan_minden[j]]
  +
  sum {j in MindenJarat}utolsojarate[j,b]*tav[hova_minden[j],depo[b]]
  +
  sum {j in MindenJarat} hozzarendel[j,b]*tav2_minden[j]
  = osszhasznalat[b];
  

s.t. osszesfogyasztas{b in Buszok}:
  osszfogyasztas[b] = osszhasznalat[b]*fogyasztas[b];

minimize osszfogyasztas_minden_buszra: sum {b in Buszok} osszfogyasztas[b];

solve;


for{b in Buszok}
{
  printf "BUSZ;JARAT;HONNAN;MIKORTOL;HOVA;MEDDIG;TAVOLSAG;TELOTT;TUTAN\n";
  for{j in MindenJarat:hozzarendel[j,b]=1}
  {
    printf "%g;%s;",b,j;  
    printf "%s;%g;%s;%g;",honnan_minden[j],mikortol_minden[j],hova_minden[j],meddig_minden[j];
    printf "%g;%g;%g\n",tav2_minden[j],toltottsege[j,b],toltottsegu[j,b];

  }
  for{j1 in MindenJarat, j2 in MindenJarat: atmegy[b,j1,j2]=1}
  {    
    printf "%g;Atmegy %s->%s;",b,j1,j2;  
    printf "%s;%g;%s;%g;",hova_minden[j1],meddig_minden[j1],honnan_minden[j2],mikortol_minden[j2];
    printf "%g;%g;%g\n",tav[hova_minden[j1],honnan_minden[j2]],toltottsegu[j1,b],toltottsege[j2,b];
  }

  for{j in MindenJarat: elsojarate[j,b]=1}
  {    
    printf "%g;Depobol odamegy %s;",b,j;  
    printf "%s;%g;%s;%g;",depo[b],mikortol_minden[j]-ido[depo[b],honnan_minden[j]],honnan_minden[j],mikortol_minden[j];
    printf "%g;%g;%g\n",tav[depo[b],honnan_minden[j]],tolteselejen[b],toltottsege[j,b];
  }

  for{j in MindenJarat: utolsojarate[j,b]=1}
  {    
    printf "%g;Depoba odamegy %s;",b,j;  
    printf "%s;%g;%s;%g;",hova_minden[j],meddig_minden[j],depo[b],meddig_minden[j]+ido[hova_minden[j],depo[b]];
    printf "%g;%g;%g\n",tav[hova_minden[j],depo[b]],toltottsegu[j,b],toltesvegen[b];
  }

  printf "\n\n\n\n";

}

end;
