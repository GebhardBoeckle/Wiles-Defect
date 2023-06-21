clearAll;

-- Variant 1 contains the version of relations with the "original" sp4 at the beginning of Section 5.3.

-- Please note: Early versions of the manuscript contained a sign error in subsection 5.3, case \cal I.
-- In several places, a factor (s+t) appeared which should be a (s-t).
-- This sign error was corrected only in the version of August 4, 2023.

-- Step 1 : Gorenstein-ness
--------------- The following code shows good mod s,t,varpi behavior ----
------- let me also compute the socle for the reduction ---
-- it works over ZZ !

-- The calculations in this step give Lemma 5.19.1. and 5.19.2.

-- In every new step: Reset all symbols to make them usable as variables again.
q = symbol q;
s = symbol s;
t = symbol t;

a = symbol a;
b = symbol b;
c = symbol c;
X = symbol X;
d = symbol d;
e = symbol e;
f = symbol f;

KK=ZZ

R = KK[a,b,X,d]

q=1;
s=0;
t=0;
e=b-s+t;
f=X;
c=b-s;

s1=d*X;
s2=e*X;
s3=f*X;
s4=a*q+ (a^2+b*c)*(1+X)-a*(1+X)^2;
s5=d^2+e*f;
s6=d*c-f*(q-1+a);
s7=d*a+f*b;
s8=e*c+d*(q-1+a);
s9=e*a-d*b;

sp1=s9+s6
sp2=s8-s7+s2
sp3=s5
sp4=s2+a*s3+s4+a*s6-b*s7-s3

Mi=ideal(a,b-s,X,d)
Is=ideal(sp1,sp2,sp3,sp4);
Ss=R/Is
basis Ss
-- Ss has basis
--  | 1 a aX aXd ad b bd X X2 X2d Xd Xd2 Xd3 d d2 d3 |
-- over the base
Ms=sub(Mi,Ss)
Js=sub(Is,Ss)
Js:Ms
---- the socle of Ss is ideal(X*d^3)

If=ideal (sp1,sp2,sp3,sp4,s1,s2,s3,s6,s7);
Sf=R/If
basis Sf
-- Sf has basis | 1 a b bd X d |
Mf=sub(Mi,Sf)
Jf=sub(If,Sf)
Jf:Mf
---- the socle of Sf is ideal(b*d)
--
-- in both, the original and the alternative, the socles are the same


-- Step 2 : generic smoothness
--------------- The following code shows generic smoothness ----

-- In every new step: Reset all symbols to make them usable as variables again.
q = symbol q;
s = symbol s;
t = symbol t;

a = symbol a;
b = symbol b;
c = symbol c;
X = symbol X;
d = symbol d;
e = symbol e;
f = symbol f;


KK=QQ[q,s,t]

R = KK[a,b,c,X,d,e,f]

-- These are the relations r_i from Lemma 5.2
s1=d*X;
s2=e*X;
s3=f*X;
s4=a*q+ (a^2+b*c)*(1+X)-a*(1+X)^2;
s5=d^2+e*f;
s6=d*c-f*(q-1+a);
s7=d*a+f*b;
s8=e*c+d*(q-1+a);
s9=e*a-d*b;

-- Relations given at beginning of section 5.3. This is the version with the "original" sp4.
sp1=s9+s6
sp2=s8-s7+s2
sp3=s5
sp4=s2+a*s3+s4+a*s6-b*s7-s3

I=ideal (sp1,sp2,sp3,sp4);
J=ideal(a,b-s,c,X,d,e-t,f)
S=R/J

JacI=sub(jacobian(I),S)
minors(4,JacI)

-- The result is (s-t)t^2*gcd(t,s,(q-1))
-- This is Lemma 5.19.3


-- Step 3 : The annihilator of I_\infty
------------- Here comes the third important piece, namely that
-------- the equations compute nicely when specializing e,f,c
-------- but not setting s,t,q-1 to zero !
----
---- the following whish list is satisfied over the ring KK:
---- S = R/I has rank 16, Sf=R/If has rank 6 and If/I has rank 10 !!
---- this is preserved under specialization KK -> E and 
---  then shows that there we have a basis.

-- In this section, Lemma 5.22 is shown.

q = symbol q;
s = symbol s;
t = symbol t;

a = symbol a;
b = symbol b;
c = symbol c;
X = symbol X;
d = symbol d;
e = symbol e;
f = symbol f;

KK=QQ[q,s,t];

R = KK[a,b,X,d];

e=b-s+t;
f=X;
c=b-s;

s1=d*X;
s2=e*X;
s3=f*X;
s4=a*q+ (a^2+b*c)*(1+X)-a*(1+X)^2;
s5=d^2+e*f;
s6=d*c-f*(q-1+a);
s7=d*a+f*b;
s8=e*c+d*(q-1+a);
s9=e*a-d*b;

sp1=s9+s6;
sp2=s8-s7+s2;
sp3=s5;
sp4=s2+a*s3+s4+a*s6-b*s7-s3

------ If=ideal (s1,s2,s3,s4,s5,s6,s7,s8,s9);
If=ideal (sp1,sp2,sp3,sp4,s1,s2,s3,s6,s7);
--- I checked by hand - easy -- that If give the same ideal
I=ideal (sp1,sp2,sp3,sp4);

S=R/I;
B=basis S

Sf=S/sub(If,S);
B1=basis Sf

Jf=sub(If,S)
Bf= basis Jf;
B2=super Bf
  
 JZ=sub(I,S)
 
  J1=JZ:Jf
  J2=JZ:J1
--- note that J2 = Jf, so there is periodicity

 use S;
  MJ=ideal(a,b-s,X,d);
   T=S/MJ;
 JJ1=sub(J1,T)


Bmut=mutableMatrix(S,1,16);
for i from 6 to 15 list
     Bmut_(0,i)=B2_(0,i-6);
     
for i from 0 to 5 list
     Bmut_(0,i)=lift(B1_(0,i),S);

Bmut

SM=mutableMatrix(S,16,16)
for i from 0 to 15 list
   for j from 0 to 15 list
      SM_(i,j)=  Bmut_(0,i)*Bmut_(0,j)  ;
 
FEB = flatten entries B;
FEBm = flatten entries Bmut;

FEBm#8
-- this is hopefully the basis Xd^3 of the socle of S/(s,t,(q-1))
-- so the basis element spanning the that socle should have index 8

MBBm=mutableMatrix(S,16,16);
for i from 0 to 15 do
    (col=coefficients( Bmut_(0,i), Monomials => FEB) ;
    for j from 0 to 15 do
       MBBm_(j,i)=col_1_(j,0)  ;)


--entries SM

MBBmi = matrix ( inverse (MBBm));
---- The matrix MBBmi satisfies   B = Bm * MBBmi

MStrConsS=mutableMatrix(S,16,16);
-- entries MStrCons

for i from 0 to 15 do
   (for j from 0 to 15 do
      (col=coefficients( SM_(i,j), Monomials => FEB) ;
      col2 = MBBmi * col_1;
      MStrConsS_(j,i)=col2_(8,0);
      );)

F = map (KK,R,{0,0,0,0});

MStrCons=mutableMatrix(KK,16,16);
-- entries MStrCons

for i from 0 to 15 do
   (for j from 0 to 15 do
      (
      MStrCons_(i,j)=F(lift(MStrConsS_(i,j),R));
      );)
-- given i,j in the middle for loop at i,j  the entry col2
-- contains the structural constants of multiplying Bm_i * Bm_j the matrx MStrCons 
-- again in terms of the Bm basis. 
-- we are then only interested in the values of the last entry
-- I hope. 
--entries MStrCons

StrCons=matrix (MStrCons);
ourdet = det StrCons
-- I find it amazing that this is 1 !!
ourinv = inverse StrCons;
CritRow=ourinv^{3};
-- third row, corresponding to the basis of the socle in FEBm of Sf/(s,t,q-1)
-- a spanning basis is bd
CritCol=submatrix(ourinv,{3})
-- third column, corresponding to the basis of the socle in FEBm of Sf/(s,t,q-1)


genOfI = matrix(Bmut)*CritCol;

G = map (KK,R,{0,s,0,0});


G(lift(genOfI_(0,0),R))
-- Supposedly this is a generator of R[I_\infty] 
-- there are lots of them ! I can multiply it with any unit of R !!

-- the results are st-t^2 in variant 1 and st in variant 2.
-- amazingly (or not?) this agrees (up to sign)
--  with the annihilator ideals computed earlier

-- This result is Corollary 5.23.


-- Step 4 : resolutions
-- Here, Corollary 5.24. is computed

q = symbol q;
s = symbol s;
t = symbol t;

a = symbol a;
b = symbol b;
c = symbol c;
X = symbol X;
d = symbol d;
e = symbol e;
f = symbol f;

KK=ZZ[s,t,q1]
R = KK[a,b,c,X,d,e,f]

q=q1+1
s1=d*X;
s2=e*X;
s3=f*X;
s4=a*q+ (a^2+b*c)*(1+X)-a*(1+X)^2;
s5=d^2+e*f;
s6=d*c-f*(q-1+a);
s7=d*a+f*b;
s8=e*c+d*(q-1+a);
s9=e*a-d*b;

sp1=s9+s6
sp2=s8-s7+s2
sp3=s5
sp4=s2+a*s3+s4+a*s6-b*s7-s3

I=ideal (sp1,sp2,sp3,sp4);
If=ideal (sp1,sp2,sp3,sp4,s1,s2,s3,s6,s7);
Istd=ideal(s1,s2,s3,s4,s5,s6,s7,s8,s9);


resIf=resolution(If, LengthLimit=>2)

PresIf=resIf.dd_2;
MapToIf=resIf.dd_1;

S=R/I;
PresIfS=sub(PresIf,S)
MapToIfS=sub(MapToIf,S)
PresIfSred=PresIfS^{4..8}

Mid=ideal(a,b-s,c,X,d,e-t,f);
T=S/Mid;

PresIfTred=sub(PresIfSred,T)
myminors5=minors(5,PresIfTred);
myminors4=minors(4,PresIfTred);
myminors3=minors(3,PresIfTred);
myminors2=minors(2,PresIfTred);
myminors1=minors(1,PresIfTred);

mingens myminors5
mingens myminors4
mingens myminors3
mingens myminors2
mingens myminors1
 
-- The minors of size ixi for i=1..4, as an ideal of O are spanned by
--  gcd (s,t,q-1)^i
-- The 5x5 minor is spanned by gcd (s,t,q-1)^3 *(st-t^2) in variant 1 
-- and by gcd (s,t,q-1)^3 *st in variant 2.


-- Step 5 : Lattices

-------------- lastly, let me compute the lattices Lambda^? in O^7 for
-- ? unipotent or the ci quotient S 
--- They allow for the computation of the last missing invariant.

--- In other words, this is Corollary 5.25.

q = symbol q;
s = symbol s;
t = symbol t;

a = symbol a;
b = symbol b;
c = symbol c;
X = symbol X;
d = symbol d;
e = symbol e;
f = symbol f;

KK=ZZ[s,t,q1]
R = KK[a,b,c,X,d,e,f]

q=q1+1
s1=d*X;
s2=e*X;
s3=f*X;
s4=a*q+ (a^2+b*c)*(1+X)-a*(1+X)^2;
s5=d^2+e*f;
s6=d*c-f*(q-1+a);
s7=d*a+f*b;
s8=e*c+d*(q-1+a);
s9=e*a-d*b;

sp1=s9+s6
sp2=s8-s7+s2
sp3=s5
sp4=s2+a*s3+s4+a*s6-b*s7-s3

I=ideal (sp1,sp2,sp3,sp4);
If=ideal (sp1,sp2,sp3,sp4,s1,s2,s3,s6,s7);
Istd=ideal(s1,s2,s3,s4,s5,s6,s7,s8,s9);

Mid=ideal(a,b-s,c,X,d,e-t,f);
T=R/Mid;

JacI=sub(jacobian(I),T)
JacIf=sub(jacobian(If),T)
JacIstd=sub(jacobian(Istd),T)

mingens minors(4,JacI)
-- (s-t)t^2 gcd(s,t,q-1)

mingens minors(4,JacIf)
-- t gcd(s,t,q-1)^3
