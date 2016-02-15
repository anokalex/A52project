
// Projet: Cassage de l'algorithme A5/2 à l'aide de polynômes
// Participants: Pressat Cyrille, Barbin Aymeric, Patel Tayyib


Ker := GF(2);
P<[X]>:=PolynomialRing(Ker,64);

nb:=0; //nombre de variables fixées

Q<[X]>:=PolynomialRing(Ker,64-nb);

nbo:=45; // a multiplier par 8 pour avoir la longueur totale en bits -- nbo = 15 par defaut


// Convertit une sequence de bits en sa valeur décimale
SeqToDec := function(seq)
	s:=0;
	for i:=1 to #seq do
		if seq[#seq+1-i] eq 1 then

			s:=s+2^(i-1);
		end if;
	end for;
	return s;
end function;


//======================================================//



//Initialisation des keyStreams

keyStreamNtoP:= [ [GF(2) |n mod 1 : n in [1..8]] ];
for i:=1 to nbo-1 do
    Append(~keyStreamNtoP, [GF(2) |n mod 1 : n in [1..8]]);
end for;

keyStreamPtoN:= [ [GF(2) |n mod 1 : n in [1..8]] ];
for i:=1 to nbo-1 do
    Append(~keyStreamPtoN, [GF(2) |n mod 1 : n in [1..8]]);
end for;


//keyStreammodNtoP et PtoN sont initialisées de telle sorte que les éléments soient reconnus comme des variables


keyStreammodNtoP:=[ [P.i -P.i: i in [1..8]] ];

for i:=1 to nbo-1 do
    Append(~keyStreammodNtoP, [P.i - P.i: i in [1..8]]);
end for;


keyStreammodPtoN:=[ [P.i -P.i: i in [1..8]] ];

for i:=1 to nbo-1 do
    Append(~keyStreammodPtoN, [P.i - P.i: i in [1..8]]);
end for;


keyStream2NtoP:=[ [Q.i -Q.i: i in [1..8]] ];

for i:=1 to nbo-1 do
    Append(~keyStream2NtoP, [Q.i - Q.i: i in [1..8]]);
end for;


keyStream2PtoN:=[ [Q.i -Q.i: i in [1..8]] ];

for i:=1 to nbo-1 do
    Append(~keyStream2PtoN, [Q.i - Q.i: i in [1..8]]);
end for;


key:=[[GF(2) |0,0,0,0,0,0,0,0],[GF(2) |0,0,1,1,1,1,1,1],[GF(2) |1,1,1,1,1,1,1,1],[GF(2) |1,1,1,1,1,1,1,1],[GF(2) |1,1,1,1,1,1,1,1],[GF(2) |1,1,1,1,1,1,1,1],[GF(2) |1,1,1,1,1,1,1,1], [GF(2) |1,1,1,1,1,1,1,1]];

frame := [GF(2) |1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];


inR1 := function(R1)
	z:= R1[19]+R1[18]+R1[17]+R1[14];
	return z;
end function;


inR2 := function(R2)
	z:= R2[22]+R2[21];
	return z;
end function;

inR3 := function(R3)
	z:= R3[23]+R3[22]+R3[21]+R3[8];
	return z;
end function;

inR4 := function(R4)
	z:= R4[17]+R4[12];
	return z;
end function;





clockR := function(R1,R2,R3,R4)
	inR1(R1);
	inR2(R2);
	inR3(R3);
	inR4(R4);
end function;




ShiftR := function(R,add)
	for i:=1 to #R-1 do
		a:=R[#R-i];
		Remove(~R, #R-i+1);
                Insert(~R, #R-i+1, a);

	end for;
	Remove(~R, 1);
        Insert(~R, 1, add);

	return R;
end function;




//======================================================//

// Initialisation des registres

init := function()

	R1 := [GF(2) |n mod 1 : n in [1..19] ];

	R2 := [GF(2) |n mod 1 : n in [1..22] ];

	R3 := [GF(2) |n mod 1 : n in [1..23] ];

	R4 := [GF(2) |n mod 1 : n in [1..17] ];


	for i:=0 to 63 do



		feedback1:= key[i div 8+1][i mod 8+1] + inR1(R1);
		feedback2:= key[i div 8+1][i mod 8+1] + inR2(R2);
		feedback3:= key[i div 8+1][i mod 8+1] + inR3(R3);
		feedback4:= key[i div 8+1][i mod 8+1] + inR4(R4);


		R1:=ShiftR(R1, feedback1);
		R2:=ShiftR(R2, feedback2);
		R3:=ShiftR(R3, feedback3);
		R4:=ShiftR(R4, feedback4);




	end for;


	for i:=1 to 22 do
		feedback1:=frame[i] + inR1(R1);
		feedback2:=frame[i] + inR2(R2);
		feedback3:=frame[i] + inR3(R3);
		feedback4:=frame[i] + inR4(R4);



		R1:=ShiftR(R1, feedback1);
		R2:=ShiftR(R2, feedback2);
		R3:=ShiftR(R3, feedback3);
		R4:=ShiftR(R4, feedback4);



	end for;



	R1[16]:=1;
	R2[17]:=1;
	R3[19]:=1;
	R4[11]:=1;

/*
	print "R1 ",R1;
	print "R2 ",R2;
	print "R3 ",R3;
	print "R4 ",R4;
*/


	return R1,R2,R3,R4;

end function;


majclock := function(R1,R2,R3,R4)


	if R4[4] eq 1 then
		a:=1;
	else
		a:=0;
	end if;

	if R4[8] eq 1 then
		b:=1;
	else
		b:=0;
	end if;

	if R4[11] eq 1 then
		c:=1;
	else
		c:=0;
	end if;

	somme:=a+b+c;
	feedback1:=inR1(R1);
	feedback2:=inR2(R2);
	feedback3:=inR3(R3);
	feedback4:=inR4(R4);
	if somme gt 1 then
		majbit:=1;
	else
		majbit:=0;
	end if;

	if R4[4] eq majbit then
		R2:=ShiftR(R2,feedback2);

	end if;

	if R4[8] eq majbit then
		R3:=ShiftR(R3,feedback3);

	end if;

	if R4[11] eq majbit then

		R1:=ShiftR(R1,feedback1);

	end if;

	R4:=ShiftR(R4,feedback4);

	return R1,R2,R3,R4;


end function;

//======================================================//


majR1 := function(R1)
	return R1[13]* (R1[15]-1) + (R1[15]-1)*R1[16] + (R1[16]*R1[13]);
end function;


majR2 := function(R2)
	return  ( R2[10]* R2[14] + (R2[17]-1)*R2[14] + (R2[17]-1)*R2[10] )  ;
end function;


majR3 := function(R3)
	return  (R3[14]-1)*R3[17] + R3[17]*R3[19] + R3[19]*(R3[14]-1) ;
end function;

//======================================================//

output:=function(R1,R2,R3)
	return majR1(R1)+R1[19]+majR2(R2)+R2[22]+majR3(R3)+R3[23];
end function;


//======================================================//

// Algo A5


//Variable globale pour recuperer la KeyStream après l'exec de outputKeyStream



outputKeyStream:=function(R1,R2,R3,R4,keyStreamNtoP,keyStreamPtoN,keyStream,aff)
    fin:=nbo*8-1;

	for i:=1 to 100 do

		R1,R2,R3,R4:=majclock(R1,R2,R3,R4);
	end for;

	if (aff eq 0) then
		print "R1 après 100 = ", R1;
	end if;

	for i:=0 to fin do
		keyStreamNtoP[i div 8 +1][i mod 8 + 1]:= output(R1,R2,R3);
		R1,R2,R3,R4:=majclock(R1,R2,R3,R4);
	end for;





	for i:=0 to fin do
		keyStreamPtoN[i div 8 +1][8-(i mod 8)]:=output(R1,R2,R3);
		R1,R2,R3,R4:=majclock(R1,R2,R3,R4);

	end for;

	if (aff eq 0) then
		print "keystream n à p";
	end if;


	for i:=1 to nbo do
		//Append(~keyStream, keyStreamNtoP[i]);
		keyStream:=keyStream cat[keyStreamNtoP[i]];
		if (aff eq 0) then
			printf "%h ",SeqToDec(keyStreamNtoP[i]),"  ";
		end if;
	end for;

	print " ";

	for i:=1 to nbo do
		keyStream:=keyStream cat[keyStreamPtoN[i]];
		//Append(~keyStream, keyStreamPtoN[i]);

		if (aff eq 0) then
			printf "%h ", SeqToDec(keyStreamPtoN[i])," ";
		end if;
	end for;

	print "";
    //print "Voici les 2 KeyStream";
    //print keyStreamPtoN[15],keyStreamNtoP[15];
	return keyStream;

end function;

//Partie suivante: Début de l'attaque: On se donne la KeyStream et R4, on veut déterminer R1,R2 et R3


//======================================================//

rev:=function(ks,r,res,keySNtoP,keySPtoN)

	K1B:=[P.i: i in [1..19]];
	K2B:=[P.i: i in [20..41]];
	K3B:=[P.i: i in [42..64]];
    res:=outputKeyStream(K1B,K2B,K3B,r,keySNtoP,keySPtoN,res,1);
    return res;
end function;


//======================================================//

geneqs:=function(ks1,ks2,ksol)
       for i:=1 to nbo*2 do
		for j:=1 to 8 do
			ksol[(i-1)*8+j]:=ks1[i][j]-ks2[i][j];
        	end for;
    	end for;
    return ksol;
end function;


//===================================================//

//if tabfixe[i]=0 alors le bit en position i de la concatenation de R1,R2 et R3 est connu et vaut Conc[i]. Si tabfice[i]=1, alors le bit est inconnu et on utilise une variable

revpart:=function(res,Conca,Reg4,keySNtoP,keySPtoN,tabfixe)
    K1B:=[Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1];
    K2B:=[Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1];
    K3B:=[Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1,Q.1];
    cpt:=1;
    for i:=1 to 19 do
        if (tabfixe[i] eq 0) then
            K1B[i]:=Conca[i];
        else
            K1B[i]:=Q.cpt;
            cpt:= cpt+1;
        end if;
    end for;
    for i:=20 to 41 do
        if (tabfixe[i] eq 0) then
            K2B[i-19]:=Conca[i];
        else
            K2B[i-19]:=Q.cpt;
            cpt:=cpt+1;
        end if;
    end for;
    for i:=42 to 64 do
        if (tabfixe[i] eq 0) then
            K3B[i-41]:=Conca[i];
        else
            K3B[i-41]:=Q.cpt;
            cpt:=cpt+1;
        end if;
    end for;
    //print K1B,K2B,K3B;
    res:=outputKeyStream(K1B,K2B,K3B,Reg4,keySNtoP,keySPtoN,res,1);

    return res;
end function;


//===================================================//
gentabfix:=function(tab,nbf)
    res:=[];
    for i:=1 to #tab do
    	Append(~res,1);
    end for;
    for i:=1 to nbf do
    	res[i]:=0;
    end for;
    return res;
end function;

//======================================================//
//Partie Execution

R1,R2,R3,R4:=init();
keyS:=[];


keyS:=outputKeyStream(R1,R2,R3,R4,keyStreamNtoP,keyStreamPtoN,keyS,0);
//keyS;

print "-------------------------------------";
print "\n\n!Premiere attaque de A5/2!\n\n";

print "Etape 1:Génération d'une nouvelle keyStream en remplaçant le contenu de R1,R2 et R3 par des variables.On fournit alors ces nouveaux registres et R4 à la fonction outputKeyStream.";
kB:=[];
kB:=rev(keyS,R4,kB,keyStreammodNtoP,keyStreammodPtoN);
print "Le résultat est stocké dans kB";
print "------------------------------------";
//kB;
ksolu:=[P.i-P.i: i in [1..64]];
resfin:=nbo*2*8;
ksolu:=ksolu cat[i -i:i in [1..resfin-64]];

//ksolu;
ksolu:=geneqs(kB,keyS,ksolu);

print "\nEtape 2:Génération d'équations en reprenant la keyStream originelle et en y soustrayant la keyStream de l'étape 1 (Par définition, le résultat doit être 0)\n";

print "Le résultat est stocké dans ksolu.\n";
print "-----------------------------------";
Conc:=[];
for i:=1 to 19 do
	Conc[i]:=R1[i];
end for;
for i:=20 to 41 do
	Conc[i]:=R2[i-19];
end for;
for i:=42 to 64 do
	Conc[i]:=R3[i-41];
end for;

print "\nEtape 3:Vérification de la bonne génération d'équations\n";



print "Concaténation des 3 registres réels R1,R2 et R3 (stockée dans Conc)\n";
Conc;
verif:=[];
boolverif:=0;
print "";
for i:=1 to resfin do
	inter:=Evaluate(ksolu[i mod 8 +1],Conc);
	//print inter;
	if (inter eq 1) then
		boolverif:=1;
		print i,ksolu[i mod 8 +1];
	end if;
	Append(~verif,inter);
end for;
print "\nEn évaluant ksolu en Conc, on doit obtenir 0 pour toutes les composantes\n";
verif;
if (boolverif eq 0) then
	print "\nOn obtient bien",resfin,"=",nbo*2,"*8 zeros\n";
else
	print "\nLes équations générées sont fausses\n";
end if;
print "--------------------------";

print "\nEtape 4:Résolution des équations\n";

//Syscat?
//ksolu:=Syscat([P.i*P.i-P.i:i in [1..64]]);
print "On vérifie que les polynomes composant ksolu sont bien de degré 2\n";
resu:=[ Degree(p): p in ksolu];
blv:=0;
for i:=1 to resfin do
	if (resu[i] ne 2) then
		blv:=1;
        print i, "Degre<2";
	end if;
end for;
print resu;
if (blv eq 1) then
	print "Error";
else

	print "\nOK\n";
end if;

EqF:=[P.i^2-P.i : i in [1..Rank(P)]];

ksolu:=[NormalForm(p,EqF) : p in ksolu];
ksolu:=ksolu cat EqF;



print "--------------------------";
print "\nEtape 4bis: Résolution des équations avec ",nb," valeurs fixées\n";


//#ksolu;

tabf:=gentabfix(Conc,nb);
//tabf;
ksol2:=[];
ksol2:=revpart(ksol2,Conc,R4,keyStream2NtoP,keyStream2PtoN,tabf);
kresfix:=[Q.i-Q.i: i in [1..64-nb]];
kresfix:=kresfix cat[i -i:i in [1..resfin-64+nb]];
//ksolu;
kresfix:=geneqs(ksol2,keyS,kresfix);

EqF:=[Q.i^2-Q.i : i in [1..Rank(Q)]];

kresfix:=[NormalForm(p,EqF) : p in kresfix];
kresfix:=kresfix cat EqF;
SetVerbose("Faugere",1);
time V:=VarietySequence(Ideal(kresfix));
print "\nRésolution terminée, résultat dans V\n";

print "\nOn vérifie si les valeurs de Conc de",nb+1,"à 64 forment bien V\n";
print "Voici le contenu de Conc de",nb,"+1 =",nb+1, "à 64:\n";
Conc[nb+1..64];

print "Voici le contenu de V: \n";
V;
print "\nTest booléen\n";
Conc[nb+1..64] in V;


//





/////////////////////// ATTAQUE N°2//////////////////////////////////////////


/*


P_2<[X]> := PolynomialRing(K,456);


G:=Matrix(Ker,456,184,[Random(Ker) : i in [1 .. 456*184]]); // matrice de correction d'erreur
Code:=LinearCode(Transpose(G));
Hp:=ParityCheckMatrix(Code);
H:=ChangeRing(Hp,P_2);                                      // matrice de parité
Parent(H);

G:=ChangeRing(G,P_2);

k_alea:=Matrix(P_2,456,1,[Random(Ker) : i in [1..456]]);     // keystream de vérification

k:=Matrix(P_2,456,1,[P_2.i : i in [1..456]]);             // keystream que l'on cherche



P1:=Matrix(P_2,184,1,[Random(Ker) : i in [1 .. 184]]);      // message de base
P2:=Matrix(P_2,184,1,[Random(Ker) : i in [1 .. 184]]);
P3:=Matrix(P_2,184,1,[Random(Ker) : i in [1 .. 184]]);


C1:=G*P1 + k_alea;                                        // message crypté et corrigé capté dans le réseau par l'attaquant
C2:=G*P1 + k_alea;
C3:=G*P1 + k_alea;


systeme1:= H*(C1) - H*k;                               
systeme2:= H*(C2) - H*k;
systeme3:= H*(C3) - H*k;





seq:=[];

for i:=1 to 272 do
	Append(~seq,systeme1[i][1]);
end for;

for i:=1 to 272 do
	Append(~seq,systeme2[i][1]);
end for;

for i:=1 to 272 do
	Append(~seq,systeme3[i][1]);
end for;




SetVerbose("Faugere",1);

I:=Ideal(seq);

V:=VarietySequence(I);
V;


*/
