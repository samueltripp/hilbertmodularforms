load "config.m";

_<x>:=PolynomialRing(Rationals());
F := NumberField(x^2-5);
prec := 300;
M := HMFSpace(F,prec);
A := SiegelEisensteinPullback(M,6);
