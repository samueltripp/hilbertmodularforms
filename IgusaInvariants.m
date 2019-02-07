////////////////////////////
///// IGUSA Invariants /////
////////////////////////////

/*
intrinsic Cohen(D::RngIntElt,s::RngIntElt) -> RngIntElt
{This is an implementation of Cohens function on page 6 of https://arxiv.org/pdf/1205.6255.pdf}
output := 0;
 s := Integers()!s;
if D eq 0 then
  output := Evaluate(RiemannZeta(),2*s-1);
 else
   if (D mod 4 eq 2) or (D mod 4 eq 3) then 
		       output := 0;
   else 
   D0 := Discriminant(QuadraticField(D));
   f:= Integers()!SquareRoot(Integers()!D/D0);
     for i := 1 to f do
		if (f mod i) eq 0 then
			       output := output + MoebiusMu(i)*(i^(-s))*DivisorSigma(1-2*s,f div i)*KroneckerSymbol(D0,i);
end if;
end for;
output := output * Evaluate(LSeries(KroneckerCharacter(D0)),s);
end if;
end if;
return output;
end intrinsic;
*/

intrinsic Cohen(k::RngIntElt, D::RngIntElt) -> any
 {Does Something}
 out := 0;
 s := k+1;
 D0 := Discriminant(QuadraticField(D));
 f:= D div D0;
 for i := 1 to f do
	    if (f mod i) eq 0 then
			   out := out + MoebiusMu(i)*KroneckerSymbol(D0,i)*i^(s-2)*DivisorSigma(2*s-3,f div i);
			   end if;

	    end for;
	    out := out * Evaluate(LSeries(KroneckerCharacter(D0)),2-s);
	    return out;


 end intrinsic;



 intrinsic alpha(D::RngIntElt,k::RngIntElt) -> any
 {Does Something}
 if D eq 0 then return 1; end if;
 return Cohen(k-1,D)/Evaluate(RiemannZeta(),3-2*k);
 end intrinsic;

 
intrinsic SiegelCoeff(k::RngIntElt,m1::RngIntElt,m::RngIntElt,m2::RngIntElt) -> RngIntElt
{Takes in an element of Sym_2(Z) and an Eisenstein series indexed by k and returns the associated coeff}
 if (m1 eq 0) and (m eq 0) and (m2 eq 0) then return 1; end if;
coeff:=0;
gcd := GreatestCommonDivisor(m1, GreatestCommonDivisor(m, m2));
for i := 1 to gcd do 
	   if gcd mod i eq 0 then 
		    coeff:=coeff+i^(k-1)*alpha((m*m-4*m1*m2) div (i*i),k);
end if;
end for;
 
 coeff := coeff*-2*k/BernoulliNumber(k);
return coeff;
 
end intrinsic;
 
/* All the following commented out code relies on narrow class number 1, 
 i.e. it is built in to be working over Z_F. This was generalized in Igusa.m
intrinsic PSD(a::RngIntElt, b::RngIntElt, d::RngIntElt, m2::FldRatElt) -> any
 {Does something}
return -d*m2*m2+4*a*m2+2*b*d*m2-b*b;
end intrinsic; 

intrinsic PSDDerivative(a::RngIntElt, b::RngIntElt, d::RngIntElt, m2::FldRatElt) -> any
 {Does Something}
return -2*d*m2+4*a+2*b*d;
end intrinsic;

intrinsic PSD(a::RngIntElt, b::RngIntElt, d::RngIntElt, m2::RngIntElt) -> any
 {does something}
return PSD(a,b,d,Rationals()!m2);
end intrinsic;

intrinsic PSDDerivative(a::RngIntElt, b::RngIntElt, d::RngIntElt, m2::RngIntElt) -> any
{does something}
return PSDDerivative(a,b,d,Rationals()!m2);
end intrinsic;

intrinsic coeff(a::RngIntElt, b::RngIntElt, d::RngIntElt, SiegelWeight::RngIntElt) -> any
{Does something}
coeff := 0;
if PSD(a,b,d,(2*a+b*d)/d) lt 0 then return coeff; end if;
if PSD(a,b,d,(2*a+b*d)/d) eq 0 then 
	if (2*a+b*d) mod d eq 0 then
		       m2 := (2*a + b*d) div d; 
                       m := b - m2*d;
                       m1 := ((4*a+2*b*d-2*m*d-m2*d*d-m2*d) div 4);
        return SiegelCoeff(SiegelWeight,m1,m,m2);
end if;
return coeff;
end if;

if (PSD(a,b,d,0) lt 0) and (PSDDerivative(a,b,d,0) lt 0) then return coeff; end if;

m2 := 0;
notDone := true;
addCoeff := false;
 while notDone do
		if PSD(a,b,d,m2) ge 0 then addCoeff := true; 
		else addCoeff := false;
 end if;
 
 if (PSDDerivative(a,b,d,m2) lt 0) and (PSD(a,b,d,m2) lt 0) then notDone := false; end if;
 
 m := b - m2*d;
 m1 := ((4*a+2*b*d-2*m*d-m2*d*d-m2*d) div 4);
 if addCoeff then coeff := coeff + SiegelCoeff(SiegelWeight, m1, m, m2); end if;
 m2 := m2+1;
end while;
 
return coeff;
end intrinsic; 
/*
intrinsic MakePositive(gen::RngQuadElt,ZF::RngQuad) -> any
{does Something}
if IsTotallyPositive(gen) then return gen; end if;
if IsTotallyPositive(-1*gen) then return -1*gen; end if;
fu := FundamentalUnit(ZF);
if IsTotallyPositive(fu*gen) then return fu*gen; end if;
return -1*fu*gen;
end intrinsic;

intrinsic GetAandB(gen::RngQuadElt, ZF::RngQuad, w::RngQuadElt) -> any
{does something}
omega := w + Discriminant(ZF)/2;
ord := Order([1,omega]:IsBasis:=true);
return ord!gen;
  end intrinsic;

*/ 

intrinsic SiegelEisenstein(k::RngIntElt,D::RngIntElt,prec::RngIntElt) -> any
{Does Something}

D0:=Discriminant(QuadraticField(D));
F:=QuadraticField(D0);
M:= HMFSpace(F,prec);
ZF<w>:=Integers(F);
N:=ideal<ZF|{1}>;
I:=Ideals(M);
coeffs := [#I];
for i:= 1 to #I do
	  _,primGen := IsPrincipal(I[i]);
posPrimGen := MakePositive(primGen,ZF);
a:=GetAandB(posPrimGen,ZF,w);
icoeffs[i]:=Round(coeff(Integers()!a[1],Integers()!a[2],D0,k));
end for;
Ek:=HMF(M,N,[k,k],coeffs);
g,r:=ConstructGeneratorsAndRelations(M,N,2,k);
temp:=g[k];
temp[#temp+1]:=Ek;
g[k]:=temp;
g,r:=Relations(M,g,r,k);
return g,r;
end intrinsic;

