"""Exhaust the cofactor words for cycles of length <= 7 with minimum above a certified bound."""
from functools import cache
from math import isqrt
import json
from verify import check

@cache
def divisors(n):
    small = [d for d in range(1,isqrt(n)+1) if n%d==0]
    return small + [n//d for d in reversed(small) if d*d!=n]

def words(product, length):
    if length==1:
        yield (product,)
        return
    for d in divisors(product):
        for tail in words(product//d,length-1):
            yield (d,)+tail

@cache
def prime(n):
    if n<2 or n%2==0:
        return n==2
    return all(n%d for d in range(3,isqrt(n)+1,2))

def candidate(word, d0):
    M,C,d = 1,0,d0
    for m in word:
        C,M,d = 10*C+d*M,M*m,d*pow(m,-1,10)%10
    gap = M-10**len(word)
    if C%gap:
        return None
    p=C//gap
    return p if p%10==d0 else None

def check_orbit(p, word):
    q = p
    for m in word:
        if q < p or not prime(q):
            return False
        s, rem = divmod(10*q+q%10,m)
        if rem or s<2 or not prime(s):
            return False
        # For a prime proposed successor, it suffices to examine prime divisors of m.
        if m>s and any(d>s and prime(d) for d in divisors(m)):
            return False
        q=s
    return q==p

def search(bound, maximum_length):
    results=[]
    for n in range(1,maximum_length+1):
        cap=(10*bound+9)**n//bound**n
        num_products=num_words=integral=0
        cycles=[]
        for M in range(10**n+1,cap+1,10):
            num_products+=1
            for w in words(M,n):
                num_words+=1
                if w[0]>=11:  # At the minimum the first edge cannot strictly descend.
                    continue
                for d in (1,3,7,9):
                    p=candidate(w,d)
                    if p is None or p<=bound:
                        continue
                    integral+=1
                    if check_orbit(p,w):
                        cycles.append([p,w])
        results.append(dict(n=n,max_product=cap,products=num_products,ordered_words=num_words,
                            integral_above_bound=integral,cycles=cycles))
    return results

if __name__=='__main__':
    bound=10**6
    check('million.tsv.gz',bound)
    print(json.dumps(search(bound,7),indent=2))
