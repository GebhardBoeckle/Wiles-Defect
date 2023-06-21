clearAll;

-- Variant 2 is the s=t case.

-- Step 0: Generate the relations
-- This corresponds to the calculations done in Section 5.1.
-- Step 0 is identical for variants 1 and 2.

KK=ZZ[q];
R=KK[a,b,c,X,d,e,f];
A = mutableMatrix(R,2,2);
A_(0,0)=q+a;
A_(0,1)=b;
A_(1,0)=c;
A_(1,1)=1-X-a;
print A
J=ideal(d,e,f,q-det matrix(A) );

N = mutableMatrix(R,2,2);
N_(0,0)=d;
N_(0,1)=e;
N_(1,0)=f;
N_(1,1)=-d;
print N
AI=A-mutableIdentity(R,2);
AN=matrix(AI)|matrix(N)
I1=minors(2,AN);
I2=ideal(X);
I=I1+I2;

-- isPrime I  
-- can easily be checked by hand
-- isPrime J
-- follows from Shotton - need to look up


IJ=intersect(I,J);
-- radical(IJ)==IJ
mgIJ = mingens IJ
idIJ=ideal(mgIJ)
-- this is the ring considered in Shotton
-- the interesction of steinberg and unramified with fixed character


rr1=-X*f;
rr2=-X*e;
rr3=d^2 + e*f;
rr4= a*d + b*f + X*d;
rr5= b*d - a*e - X*e;
rr6= a*d + b*f;
rr7= c*e - b*f + (q - 1)*d;
rr8= c*d - a*f - X*f + (- q + 1)*f;
rr9= a^2 + b*c + a*X + (q-1)*a + q*X;
IJ3=ideal (rr1,rr2,rr3,rr4,rr5,rr6,rr7,rr8,rr9);

r1=X*f;
r2=X*e;
r3=d^2 + e*f;
r4= X*d;
r5= b*d - a*e;
r6= a*d + b*f;
r7= c*e - b*f + (q - 1)*d;
r8= c*d - a*f + (- q + 1)*f;
r9= a^2 + b*c + a*X + (q-1)*a + q*X;

IJ2=ideal (r1,r2,r3,r4,r5,r6,r7,r8,r9);
IJ2==IJ 
IJ3==IJ



-- Step 1 : Gorenstein-ness
--------------- The following code shows good mod s,t,varpi behavior ----
------- let me also compute the socle for the reduction ---

-- The calculations in this step confirm Lemma 5.4.3.

-- Furthermore, Lemma 5.27.1 and 5.27.2 are shown/calculated here.


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


--  The code works over ZZ

R = ZZ[a,b,X,d]

q=1;
s=0;
t=0;
e=b-s+t;
f=X;
c=b-s; 

-- Following the computations for Proposition 5.4, one finds that
-- a^4, X+a^2-a^3,b^2,d^2 are relations !
-- This gives a rank 16 CI cover. However I could not find lifts
-- for a lifted CI cover of rank 16 and such that the agumentation is 
-- a smooth point on the generic fiber and so that Step 3 below works.
-- Eventually another kind of relation ideal for degree 16 worked better.
-- it too has a simple reduction in the sense of Proposition 5.4:


r1= X*f;
r2= X*e;
r3= X*d;
r4= d^2 + e*f;
r5= b*d - a*e;
r6= a*d + b*f;
r7= c*e - b*f + (q - 1)*d;
r8= c*d - a*f + (- q + 1)*f;
r9= a^2 + b*c + a*X + (q-1)*a + q*X;

Iun = ideal (r1,r2,r3,r4,r5,r6,r7,r8,r9);


-- the following are the equations for the CI cover for the case s = t
-- variant 2
sp1= r7+r2
sp2= r4-r2
sp3=  r1 +(q-1)*(r6-r2) +r2
sp4= r9-r7-r2


Jun=ideal( sp1,  sp2,  sp3,  sp4)
-- Jun=ideal(b^2,d^2,X^2+(q-1)*ad,X*(1+a)+a^2)


-- The formal smoothness at the augmentation needed the extra summand
-- +(q-1)*(r6-r2) for sp3 the +r2 was an alternative that worked for 
-- s=t where the usual relations do not produce smoothness

mR = ideal(a,b,d,X)


S=R/Iun;
basis S

-- basis 1, a, b, b*d, X ,d
-- the ideal Iun is the same in both variants.


mS=sub(mR,S)
IS=sub(Iun,S)
socleS=IS:mS



-- ring is Gorenstein ! A socle generator is
--   b*d
-- 

tS=R/Jun;
basis tS

-- basis of the CI cover for variant 2 is
-- 1 a ab abd aX aX2 aX2d aXd ad b bd X X2 X2d Xd d 

mtS=sub(mR,tS)
ItS=sub(Jun,tS)
socletS = ItS:mtS


--  it is clear that R/Jun is a global c.i. because dim R/Jun = dim R - min number of gens of Jun
-- 
-- a socle generator in variant 2 is
-- a*X^2*d


-- Step 2 : smoothness at augmentation point on generic fiber

-- This step corresponds to Lemma 5.27.3, but in the s=t case. 
-- cf. Remark 5.33 instead.

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



r1= X*f;
r2= X*e;
r3= X*d;
r4= d^2 + e*f;
r5= b*d - a*e;
r6= a*d + b*f;
r7= c*e - b*f + (q - 1)*d;
r8= c*d - a*f + (- q + 1)*f;
r9= a^2 + b*c + a*X + (q-1)*a + q*X;


Iun=ideal (r1,r2,r3,r4,r5,r6,r7,r8,r9);


sp1= r7+r2
sp2= r4-r2
sp3=  r1 +(q-1)*(r6-r2) +r2
sp4= r9-r7-r2

-- in sp3, the second summand was found by trial and error; 
-- all ri were tried and then a suitable linear combination worked better
-- for variant 2 adding r2 was another guess.
--
-- 3 requirements had to be satisfied at once:
-- being a CI cover, finite over the base Z, after reduction modulo 
-- a suitable set of variables
-- being smooth at the given augmentation
-- having a nice basis without partial evaluation at the augmentation 
-- as is done in Step 1 

Jun=ideal( sp1 ,  sp2 ,  sp3 ,  sp4)

J=ideal(a,b-s,c,X,d,e-t,f)
S=R/J

JacJun=sub(jacobian(Jun),S)
minors(4,JacJun)
mingens(minors(4,JacJun))


--  4 x 4 minors in the modified case
--  q2s2t2-q2st3-2qs2t2+2qst3+s2t2+qt3-st3-t3 =st2(s-t)(q-1)2+(q-1)t3 
--  q2s3t-q2st3-2qs3t+2qst3+s3t+qst2+qt3-st3-st2-t3= st(s2-t2)(q-1)2+(q-1)t3
--  q3s2t-q3st2-3q2s2t+3q2st2+3qs2t+q2t2-3qst2-s2t-2qt2+st2+t2
--    = st(s-t)(q-1)3 + t2(q-1)2
--
-- substituting s=t in modified minors gives simple expression for gcd
--  (q-1)t2 gcd(t,q-1)



-- Step 3 : The annihilator of I_\infty
------------- Here comes the third important piece, namely that
-------- the equations compute nicely when specializing e,f,c
-------- but not setting s,t,q-1 to zero !

-- This step corresponds to Lemma 5.30.

----
---- the following wish list is satisfied over the ring KK:
---- S = R/I has rank 6, Sf=R/If has rank 16 and If/I has rank 10 !!
---- this is preserved under specialization KK -> E and 
---  then shows that there we have a basis.
--  one has to work over QQ, not ZZ due to Macaulay2

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


KK=QQ[q1,s,t]

R=KK[a,b,X,d]


e=b-s+t;
f=X;
c=b-s;


r1= X*f;
r2= X*e;
r3= X*d;
r4= d^2 + e*f;
r5= b*d - a*e;
r6= a*d + b*f;
r7= c*e - b*f + q1 *d;
r8= c*d - a*f - q1*f;
r9= a^2 + b*c + a*X + q1*a + (1+q1)*X;


-- equations for the CI cover in variant 2 - as before
sp1= r7+r2
sp2= r4-r2
sp3=   r1 + q1*(r6-r2) +r2
sp4= r9-r7-r2

If=ideal (sp1,sp2,sp3,sp4);

Sf=R/If;
B=basis Sf
-- the basis if Sf has cardinality 16
-- the usual basis   
--  1 a ab abd aX aX2 aX2d aXd ad b bd X X2 X2d Xd d |


I=ideal (r1,r2,r3,r4,r5,r6,r7,r8,r9);
Jf0=sub(I,Sf)
Jf=ideal(mingens(Jf0))
-- including the mingens improves the computation


Bf= basis Jf
B2=super Bf
-- the basis if Jf0 has cardinality 10
-- | Xd  X2  X2d  ad+(s-t)X  aX-bd+q1X+sd  aX2+X2d+q1X2+(q1s-q1t+t)Xd  aX2d+q1X2d  aXd+q1Xd  ab-bd+(-s+t)a  abd+(-s+t)ad |
-- unexpected

S=Sf/Jf;
B1=basis S
-- the basis of S has cardinality 6
-- the usual basis     1 a b bd X d

---  6+10 =16
-- the dimension are as in the mod (s,t,q1) specialization in Step 1 !!

-- we need to identify the critical indices and the total size.
Bmut=mutableMatrix(Sf,1,16);
for i from 6 to 15 do
     Bmut_(0,i)=B2_(0,i-6)
     

for i from 0 to 5 do
     Bmut_(0,i)=lift(B1_(0,i),Sf);

Bmut

SM=mutableMatrix(Sf,16,16)
for i from 0 to 15 list
   for j from 0 to 15 list
      SM_(i,j)=  Bmut_(0,i)*Bmut_(0,j)  ;


FEB = flatten entries B;
FEBm = flatten entries Bmut;


-- here’s the code that justifies the choice of index 12 below 
-- by printing the entries of FEBm 

for i from 0 to 15 do
   print sub(lift(FEBm#i,R),{s=>0,t=>0,q1=>0});

FEBm#12
-- 
-- 
-- FEBm#12 is the only basis element that 
-- contains a*X^2*d  (mod s=0,t=0,q1=0)
-- [IN THE MODIFIED CASE]
-- Observe that the monomial  a*X*^2d  is the socle in Step 1.
-- so e_12^* is non-zero on the mod  (mod s=0,t=0,q1=0) socle



MBBm=mutableMatrix(Sf,16,16);
for i from 0 to 15 do
    (col=coefficients( Bmut_(0,i), Monomials => FEB) ;
    for j from 0 to 15 do
       MBBm_(j,i)=col_1_(j,0)  ;)

---- The matrix MBBm is the base change matrix such that
----  Bm = B * MBBm


MBBmi = matrix ( inverse matrix (MBBm));
---- The matrix MBBmi satisfies   B = Bm * MBBmi



MStrConsS=mutableMatrix(Sf,16,16);
-- entries MStrCons

---- observe the 12 in the following code !!!


for i from 0 to 15 do
   (for j from 0 to 15 do
      (col=coefficients( SM_(i,j), Monomials => FEB) ;
      col2 = MBBmi * col_1;
      MStrConsS_(j,i)=col2_(12,0);
      );)


F = map (KK,R,{0,0,0,0});

MStrCons=mutableMatrix(KK,16,16);

-- entries MStrCons

for i from 0 to 15 do
   (for j from 0 to 15 do
      (MStrCons_(i,j)=F(lift(MStrConsS_(i,j),R));
      );)
-- given i,j in the middle for loop at i,j  the entry col2
-- contains the structural constants of multiplying Bm_i * Bm_j the matrx MStrCons 
-- again in terms of the Bm basis. 
-- we are then only interested in the coefficient of the basis element with index 12


StrCons=matrix (MStrCons);
ourdet = det StrCons
-- the determinant has value 1  !!


ourinv = inverse StrCons;
CritRow=ourinv^{3};
-- the socle in FEBm of Sf/(s,t,q1) is b*d; this is at position 3
-- (with the count starting at 0) 
--  the basis elts of the quotient over ZZ are 1 a b X d bd


CritCol=submatrix(ourinv,{3})
-- third column, corresponding to the basis of the socle in FEBm 
-- of Sf/(s,t,q1)


genOfI = matrix(Bmut)*CritCol
-- This is a generator of R[I_\infty] 
-- there are lots of them ! I can multiply it with any unit of R !!

G = map (KK,R,{0,s,0,0});
-- the map sends a |-> 0,  b |-> s,  X |-> 0,  d |-> 0  !!
-- in particular the order of variables of R is important when defining G

G(lift(genOfI_(0,0),R))

-- the result is 
--  q1 * (-q1*s+q1*t-t)

-- This result corresponds to the one in Proposition 5.31.1, but in the s=t case. 
-- cf. Remark 5.33 instead.



-- Step 4 : resolutions

-- These calculations correspond to the one giving Proposition 5.31.2., but in the s=t case. 
-- cf. Remark 5.33 instead.

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

KK=ZZ[s,t,q1]

-- This step works over ZZ

R = KK[a,b,c,X,d,e,f]

q=q1+1;

r1= X*f;
r2= X*e;
r3= X*d;
r4= d^2 + e*f;
r5= b*d - a*e;
r6= a*d + b*f;
r7= c*e - b*f + q1*d;
r8= c*d - a*f - q1*f;
r9= a^2 + b*c + a*X + q1*a + (q1+1)*X;


sp1= r7+r2
sp2= r4-r2
sp3=  r1 +(q-1)*(r6-r2)+r2
sp4= r9-r7-r2
If=ideal (sp1,sp2,sp3,sp4);


I=ideal (sp1,sp2,sp3,sp4,r2,r3,r5,r6,r8);
Istd= ideal (r1,r2,r3,r4,r5,r6,r7,r8,r9);
-- it is important for the computation below that the first 4 gens of I
-- lie in If and hence vanish in R/If

Istd==I
---  checked that all is fine with the ideals defined.

resI=resolution(I, LengthLimit=>2)
-- R <- R^9 <- R^27
PresI=resI.dd_2;
MapToI=resI.dd_1;

S=R/If;
PresIS=sub(PresI,S)
MapToIS=sub(MapToI,S)
PresISred=PresIS^{4..8}

Mid=ideal(a,b-s,c,X,d,e-t,f);
T=S/Mid;

PresITred=sub(PresISred,T)
myminors5=minors(5,PresITred);
myminors4=minors(4,PresITred);
myminors3=minors(3,PresITred);
myminors2=minors(2,PresITred);
myminors1=minors(1,PresITred);


--mingens myfittId
mingens myminors5
mingens myminors4
mingens myminors3
mingens myminors2
mingens myminors1
 
-- The minors of size ixi for i=1..5, as an ideal of O are spanned by
--  1,1, *,  *,     and q1*t*gcd(q1,t)
--  for s=t
--
-- in variant 2  the relevant fitting ideal is generated by
--   sq1^3-tq1^3+tq1^2  = q1^2(sq1 -tq1 +t)
-- stq1^2-t2q1^2+t2q1 = tq1(sq1 - tq1 +t)
-- s2q1^2-t2q1^2+stq1+t2q1= q1(s+t)( (s-t)q1 +t)
-- ->     q1(q1,s,t)(sq1-tq1+t)  !!

-- The Fitting ideal of our interest is formed by the 5x5 minors !!
--



-- Step 5 : Lattices

-- These calculations give Proposition 5.31.3., but in the s=t case. 
-- cf. Remark 5.33 instead.

-------------- lastly, let me compute the lattices Lambda^? in O^7 for
--  the unipotent ring or its ci cover
--- They allow for the computation of the last missing invariant.
-- eventually we compute the ideals of 4-minors;
-- there index is the index of the lattices.
--- 

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

KK=ZZ[s,t,q1]

-- this step can be done over ZZ

R = KK[a,b,c,X,d,e,f]

q=q1+1;


r1= X*f;
r2= X*e;
r3= X*d;
r4= d^2 + e*f;
r5= b*d - a*e;
r6= a*d + b*f;
r7= c*e - b*f + (q - 1)*d;
r8= c*d - a*f + (- q + 1)*f;
r9= a^2 + b*c + a*X + (q-1)*a + q*X;

sp1= r7+r2
sp2= r4-r2
sp3=  r1 +(q-1)*(r6-r2) +r2
sp4= r9-r7-r2


-- I=ideal (sp1,sp2,sp3,sp4,r1,r2,r4,r5,r6);
I= ideal (r1,r2,r3,r4,r5,r6,r7,r8,r9);
If=ideal (sp1,sp2,sp3,sp4);


Mid=ideal(a,b-s,c,X,d,e-t,f);
T=R/Mid;

JacI=sub(jacobian(I),T)
JacIf=sub(jacobian(If),T)


mingens minors(4,JacIf)

--  same as in step 4 except for an additional factor of t !  here for comparison
--   sq1^3-tq1^3+tq1^2   stq1^2-t2q1^2+t2q1   s2q1^2-t2q1^2+stq1+t2q1
--  q1t(q1,s,t)(sq1-tq1+t)  !!
--  q1 t^2(q1,s,t)    for s=t


mingens minors(4,JacI)
-- t gcd(s,t,q-1)^2
-- from  | tq1^2 t2q1 stq1 t3 st2 s2t |
-- t * (q1^2 , tq1 , sq1 , t2 st s2)
-- = t*(q1,t)^2  for s=t

-- the last result is the same in both variants
-- R/I does not depend on the s_i