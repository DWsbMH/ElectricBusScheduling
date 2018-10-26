set Helyek;
param tav{h1 in Helyek, h2 in Helyek}; #km
param ido{h1 in Helyek, h2 in Helyek}; #perc

param nJarat;
set Jaratok := 1 .. nJarat;
param honnan{Jaratok} symbolic, in Helyek;
param hova{Jaratok} symbolic, in Helyek;
param mikortol{Jaratok}; #perc
param meddig{Jaratok}; #perc

#azok a járatpárok amik nem mehetnek egy busszal
set kulonbozobusz := setof{j in Jaratok, j2 in Jaratok: mikortol[j]<=mikortol[j2] && mikortol[j2]<meddig[j]+ido[hova[j],honnan[j2]] && j!=j2} (j,j2);

param nBusz;
set Buszok := 1..nBusz;

param depo{Buszok} symbolic, in Helyek;

var hozzarendel{Jaratok,Buszok}, binary;
var atmegy{Buszok,Jaratok,Jaratok}, binary;

#az adott járat az elsõ/utolsó-e annak a busznak
var elsojarate{Jaratok,Buszok}, binary;
var utolsojarate{Jaratok,Buszok}, binary;

#minden járat el legyen végezve
s.t. mindenJaratElvegezve {j in Jaratok} : sum {b in Buszok} hozzarendel[j,b]=1;


#ha nem az elsõ járata a busznak, akkor csak olyan járatot vállalhat ahol a következõ járat kezdési ideje - az aktuális járat vége között van e elégidõ hogy átjusson
s.t. OsszeferhetetlenJaratok{(j,j2) in kulonbozobusz, b in Buszok}:
  hozzarendel[j,b]+hozzarendel[j2,b]<=1;

#atmegy 1 lesz ha mindkettõhöz hozzá van rendelve é nincs köztes
s.t. Atmegyconstraint{b in Buszok, j in Jaratok, j2 in Jaratok:mikortol[j2]>meddig[j] }:
  atmegy[b,j,j2]
  + sum {jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]} hozzarendel[jkoztes,b]
  >=-1+hozzarendel[j,b]+hozzarendel[j2,b];

s.t. Atmegyconstraint_elesito{b in Buszok, j in Jaratok, j2 in Jaratok}:
  atmegy[b,j,j2]<=(hozzarendel[j,b]+hozzarendel[j2,b])/2;
  
s.t. Atmegyconstraint_elesito2{b in Buszok, j in Jaratok, j2 in Jaratok,jkoztes in Jaratok: mikortol[jkoztes]>=meddig[j] && meddig[jkoztes] <= mikortol[j2]}:
  atmegy[b,j,j2]<=1-hozzarendel[jkoztes,b];

#elso jarat beallitas -> a jaratok kozul amiket elvallal a busz, a legkisebb kezdoideju
#kezdetben minden 1
s.t. elsoInit{b in Buszok, j in Jaratok: hozzarendel[j,b]=1}:
  elsojarate[j,b]=1;

s.t. elsoBeallit{b in Buszok, j in Jaratok, j2 in Jaratok: j!=j2 && hozzarendel[j,b]=1 && hozzarendel[j2,b]=1 && mikortol[j]<mikortol[j2]}: 
  elsojarate[j2,b]<1 - elsojarate[j,b];

#utolso jarat beallitas -> a jaratok kozul amiket elvallal a busz, a legnagyobb kezdoideju
#kezdetben minden 1
s.t. utolsoInit{b in Buszok, j in Jaratok: hozzarendel[j,b]=1}:
  utolsojarate[j,b]=1;

s.t. utolsoBeallit{b in Buszok, j in Jaratok, j2 in Jaratok: j!=j2 && hozzarendel[j,b]=1 && hozzarendel[j2,b]=1 && meddig[j]>meddig[j2]}: 
  utolsojarate[j2,b]<1 - utolsojarate[j,b];

#cel a koztes km-ek minimalizalasa-minimális legyen az átjutási km : minden buszra a járatainál az utolsó helytõl a következõ helyig lévõ távolságok összege
minimize Koztestav: sum {b in Buszok, j1 in Jaratok, j2 in Jaratok} tav[hova[j1],honnan[j2]]*atmegy[b,j1,j2]
+sum {b in Buszok, j3 in Jaratok}elsojarate[j,b]*tav[honnan[j3],depo[b]]+sum {b in Buszok, j3 in Jaratok}utolsojarate[j,b]*tav[hova[j3],depo[b]];

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
