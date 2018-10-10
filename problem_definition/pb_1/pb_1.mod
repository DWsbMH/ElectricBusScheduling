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
var hozzarendel{Jaratok,Buszok}, binary;
var elsojarate{Jaratok, Buszok}, binary; #ez a járat az elsõ e ennek a busznak
#var buszjaratszam{Buszok}, integer, >=0; 

#minden busz maximum 5 járatot vállalhat
s.t. mindenBuszMaximumOtJaratot {b in Buszok} : sum {j in Jaratok} hozzarendel[j,b]<=5;

#minden járat el legyen végezve
s.t. mindenJaratElvegezve {j in Jaratok} : sum {b in Buszok} hozzarendel[j,b]=1;

#elsõ járat beállítása ha hozzarendel[j,b]=1 és ...

#ha nem az elsõ járata a busznak, akkor csak olyan járatot vállalhat ahol a következõ járat kezdési ideje - az aktuális járat vége között van e elégidõ hogy átjusson
s.t.idoKorlat {j in Jaratok} : (meddig[j]-mikortol[j])*hozzarendel[j]>=ido[honnan[j],hova[j]]+ido(aholmostvan,honnan[j]);

#cel a koztes km-ek minimalizalasa-minimális legyen az átjutási km : minden buszra a járatainál az utolsó helytõl a következõ helyig lévõ távolságok összege
minimize Koztestav {b in Buszok}: sum {j1 in Jaratok, j2 in Jaratok : j1<j2} tav[hova[j1],honnan[j2]];
end;
