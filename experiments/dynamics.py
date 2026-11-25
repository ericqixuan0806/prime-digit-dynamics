"""Exact reference dynamics and memoized factorization for certificate generation."""
from functools import cache
from math import prod
from sympy import factorint, isprime

CYCLE = (23,233,2333,23333,661,601,6011,6679,997,907,313,241,2411,
         47,53,41,137,17,59,599,857,953,9533,13619,19457,821)

def largest_prime_factor(n):
    if n < 2:
        raise ValueError("largest prime factor requires n >= 2")
    return max(map(int, factorint(n)))

def T(p):
    return largest_prime_factor(10 * p + p % 10)

@cache
def factors(p):
    n = 10 * p + p % 10
    fs = sorted(int(q) for q, e in factorint(n).items() for _ in range(e))
    if prod(fs) != n or not all(map(isprime, fs)):
        raise ArithmeticError(f"unverified factorization of {n}")
    return tuple(fs)

def orbit(p):
    """Yield through the first visit to an already encountered state, inclusive."""
    seen = set()
    while p not in seen:
        yield p
        seen.add(p)
        p = factors(p)[-1]
    yield p

def first_descent(p):
    for k,q in enumerate(orbit(p)):
        if q < p:
            return k
    return None

def increasing_chain(p, r):
    for _ in range(r):
        q = factors(p)[-1]
        if q <= p:
            return False
        p = q
    return True
