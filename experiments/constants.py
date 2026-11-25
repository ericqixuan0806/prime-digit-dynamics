"""Rational certificates for the small numerical inequalities in the explicit sieve audit."""
from fractions import Fraction as F
from math import factorial

def exp_bounds(x, n=48):
    lo=sum((x**j/F(factorial(j)) for j in range(n+1)),F(0))
    first=x**(n+1)/factorial(n+1)
    ratio=x/(n+2)
    if ratio>=1:
        raise ValueError('truncation too short')
    return lo,lo+first/(1-ratio)

h16=sum((F(1,j) for j in range(1,17)),F(0))
checks=[('exp(H16) < 30', exp_bounds(h16)[1]<30),
        ('exp(9/2) < 135', exp_bounds(F(9,2))[1]<135),
        ('exp(2) < 8',exp_bounds(F(2))[1]<8),
        ('exp(8) < 10^6',exp_bounds(F(8))[1]<10**6),
        ('exp(5) > 110',exp_bounds(F(5))[0]>110),
        ('(9/2)^2/8 > 2.50637',F(9,2)**2/8>F(250637,100000))]
if not all(ok for _,ok in checks):
    raise ArithmeticError(checks)
for label,_ in checks: print(label)
