clearAll;

R=ZZ[a,b,c,d,e,f,q]

I=ideal(d^2+e*f,q*d+c*e,q*a+c*b)

S=R/I

p=matrix{{0,e,0,-b,0,-d,0,a},{e,0,0,q,-d,0,0,c},{-d,0,q,0,-f,0,c,0}}

J=minors(3,p)

K=trim(J)

J==K

numgens(K)
