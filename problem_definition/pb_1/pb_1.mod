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
var elsojarate{Jaratok, Buszok}, binary; #ez a j�rat az els� e ennek a busznak
#var buszjaratszam{Buszok}, integer, >=0; 

#minden busz maximum 5 j�ratot v�llalhat
s.t. mindenBuszMaximumOtJaratot {b in Buszok} : sum {j in Jaratok} hozzarendel[j,b]<=5;

#minden j�rat el legyen v�gezve
s.t. mindenJaratElvegezve {j in Jaratok} : sum {b in Buszok} hozzarendel[j,b]=1;

#els� j�rat be�ll�t�sa ha hozzarendel[j,b]=1 �s ...

#ha nem az els� j�rata a busznak, akkor csak olyan j�ratot v�llalhat ahol a k�vetkez� j�rat kezd�si ideje - az aktu�lis j�rat v�ge k�z�tt van e el�gid� hogy �tjusson
s.t.idoKorlat {j in Jaratok} : (meddig[j]-mikortol[j])*hozzarendel[j]>=ido[honnan[j],hova[j]]+ido(aholmostvan,honnan[j]);

#cel a koztes km-ek minimalizalasa-minim�lis legyen az �tjut�si km : minden buszra a j�ratain�l az utols� helyt�l a k�vetkez� helyig l�v� t�vols�gok �sszege
minimize Koztestav {b in Buszok}: sum {j1 in Jaratok, j2 in Jaratok : j1<j2} tav[hova[j1],honnan[j2]];
end;
