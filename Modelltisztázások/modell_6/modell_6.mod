set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

set Jaratok;
param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc
param tav2 {Jaratok}; #km

set Toltohelyek;

param IH := max {j in Jaratok} meddig[j]; #idohorizont
param idoszelet;

set Toltojaratok := setof {t in Toltohelyek, s in 1..(IH/idoszelet)}
 t & '_' & s;

param t_hely{t in Toltojaratok} symbolic := substr(t,1,1);
param t_szam{t in Toltojaratok} := substr(t,3);

set MindenJarat := Jaratok union Toltojaratok;

param honnan_tolto {t in Toltojaratok} symbolic:= t_hely[t];
param honnan_minden{m in MindenJarat} symbolic := if m in Jaratok then honnan[m]
                        else honnan_tolto[m];

param hova_tolto {t in Toltojaratok} symbolic:= t_hely[t];
param hova_minden{m in MindenJarat} symbolic:= if m in Jaratok then hova[m]
                        else hova_tolto[m];

param mikortol_tolto {t in Toltojaratok}:= (t_szam[t]-1)*idoszelet;
param mikortol_minden{m in MindenJarat} := if m in Jaratok then mikortol[m]
                        else mikortol_tolto[m];

param meddig_tolto {t in Toltojaratok}:= (t_szam[t])*idoszelet;
param meddig_minden{m in MindenJarat} := if m in Jaratok then meddig[m]
                        else meddig_tolto[m];

param tav2_tolto {t in Toltojaratok}:= tav[t_hely[t],t_hely[t]];
param tav2_minden{m in MindenJarat} := if m in Jaratok then tav2[m]
                        else tav2_tolto[m];

set Kulonbozobusz := setof{j in MindenJarat, j2 in MindenJarat: mikortol_minden[j]<=mikortol_minden[j2] && mikortol_minden[j2]<meddig_minden[j]+ido[hova_minden[j],honnan_minden[j2]] && j!=j2} (j,j2);

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

s.t. JaratokElvegzese1 {j in Jaratok} : sum {b in Buszok} hozzarendel[j,b]=1;

s.t. JaratokElvegzese2 {j2 in Toltojaratok} : sum {b in Buszok} hozzarendel[j2,b]<=1;

s.t. OsszeferhetetlenJaratok{(j,j2) in Kulonbozobusz, b in Buszok}:
  hozzarendel[j,b]+hozzarendel[j2,b]<=1;

s.t. AtmenetKorlatozas{b in Buszok, j in MindenJarat, j2 in MindenJarat:mikortol_minden[j2]>meddig_minden[j] }:
  atmenet[b,j,j2]
  + sum {jkoztes in MindenJarat: mikortol_minden[jkoztes]>=meddig_minden[j] && meddig_minden[jkoztes] <= mikortol_minden[j2]} hozzarendel[jkoztes,b]
  >=-1+hozzarendel[j,b]+hozzarendel[j2,b];

s.t. AtmenetKorlatozas_elesito1{b in Buszok, j in MindenJarat, j2 in MindenJarat}:
  atmenet[b,j,j2]<=(hozzarendel[j,b]+hozzarendel[j2,b])/2;
  
s.t. AtmenetKorlatozas_elesito2{b in Buszok, j in MindenJarat, j2 in MindenJarat,jkoztes in MindenJarat: mikortol_minden[jkoztes]>=meddig_minden[j] && meddig_minden[jkoztes] <= mikortol_minden[j2]}:
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

s.t. KesobbiNemElso{b in Buszok, j in MindenJarat,j2 in MindenJarat: mikortol_minden[j]>mikortol_minden[j2]}:
  elsojarat[j,b] <= 0 + M * (1- hozzarendel[j2,b]);

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

s.t. KorabbiNemUtolso{b in Buszok, j in MindenJarat,j2 in MindenJarat: mikortol_minden[j]<mikortol_minden[j2]}:
  utolsojarat[j,b] <= 0 + M * (1- hozzarendel[j2,b]);

#Toltottsegi szint korlatozasok
s.t. JaratElottiToltottseg{b in Buszok, j1 in MindenJarat, j2 in MindenJarat}:
  toltottsege[j2,b]<=toltottsegu[j1,b] -tav[hova_minden[j1],honnan_minden[j2]]*fogyasztas[b]+M*(1-atmenet[b,j1,j2]);

s.t. JaratUtaniToltottseg1{b in Buszok, j in Jaratok}:
  toltottsegu[j,b]<=toltottsege[j,b]-tav[hova[j],honnan[j]]*fogyasztas[b]+M*(1-hozzarendel[j,b]);

s.t. JaratUtaniToltottseg2{b in Buszok, tj in Toltojaratok}:
  toltottsegu[tj,b]>=maxtoltes[b]-M*(1-hozzarendel[tj,b]);

s.t. OsszhasznalatKiszamitas {b in Buszok}:
  sum {j1 in MindenJarat, j2 in MindenJarat} tav[hova_minden[j1],honnan_minden[j2]]*atmenet[b,j1,j2]
  +
  sum {j in MindenJarat}elsojarat[j,b]*tav[depo[b],honnan_minden[j]]
  +
  sum {j in MindenJarat}utolsojarat[j,b]*tav[hova_minden[j],depo[b]]
  +
  sum {j in MindenJarat} hozzarendel[j,b]*tav2_minden[j]
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
  for{j in MindenJarat:hozzarendel[j,b]=1}
    printf "\tJarat %s: %s(%g) --%g--> %s(%g) (%g)->(%g)\n",j,honnan_minden[j],mikortol_minden[j],tav[honnan_minden[j],hova_minden[j]],hova_minden[j],meddig_minden[j],toltottsege[j,b],toltottsegu[j,b];
  for{j in MindenJarat: elsojarat[j,b]=1}
    printf "\tElsojarat: Depo --%g--> Jarat %s : %s(%g) -> %s(%g) (%g)->(%g)\n",tav[depo[b],honnan_minden[j]],j,depo[b],0,honnan_minden[j],mikortol_minden[j],toltottsege[j,b],toltottsegu[j,b];
  for{j in MindenJarat, j2 in MindenJarat: atmenet[b,j,j2]=1}
    printf "\tAtmenes: Jarat %s --%g--> Jarat %s : %s(%g) -> %s(%g) (%g)->(%g)\n",j,tav[hova_minden[j],honnan_minden[j2]],j2,hova_minden[j],meddig_minden[j],honnan_minden[j2],mikortol_minden[j2],toltottsege[j,b],toltottsegu[j,b];
  for{j in Jaratok: utolsojarat[j,b]=1}
    printf "\tUtolsojarat: Jarat %s --%g--> Depo : %s(%g) -> %s(%g) (%g)->(%g)\n",j,tav[hova_minden[j],depo[b]],hova_minden[j],meddig_minden[j],depo[b],meddig_minden[j]+ido[hova_minden[j],depo[b]],toltottsege[j,b],toltottsegu[j,b];
}
end;