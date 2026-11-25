"""Enumerate digit/cofactor words with one full congruence class per word."""
import json
from collections import Counter
from itertools import combinations
from math import gcd, prod
from pathlib import Path
from sympy import factorint, primerange

DIGITS = (1, 3, 7, 9)
def words(r, digit, path=()):
    if not r:
        yield path
        return
    for m in DIGITS:
        if gcd(digit,m) == 1:
            following = digit * pow(m,-1,10) % 10
            yield from words(r-1,following,path+((digit,m,following),))

def branch(path):
    M, C = [1], [0]
    for d,m,_ in path:
        C.append(10*C[-1]+d*M[-1])
        M.append(m*M[-1])
    Q, d0 = 10*M[-1], path[0][0]
    residues = [a for a in range(d0,Q,10)
                if all((10**i*a+c)%m == 0 for i,(m,c) in enumerate(zip(M,C)))]
    if len(residues) != 1:
        raise ValueError((path,residues))
    a, = residues
    forms = [(10**i*Q//m,(10**i*a+c)//m) for i,(m,c) in enumerate(zip(M,C))]
    dets = [A*D-B*C1 for (A,B),(C1,D) in combinations(forms,2)]
    if not all(x>0 for x in dets):
        raise ArithmeticError(dets)
    bad = sorted({int(p) for x in [u for u,_ in forms]+dets for p in factorint(x)})
    def root_count(p):
        roots = set()
        for A,B in forms:
            if A%p:
                roots.add((-B*pow(A,-1,p))%p)
            elif B%p == 0:
                return p
        return len(roots)
    contents = [gcd(A,B) for A,B in forms]
    small = [int(p) for p in primerange(2,len(forms)+1)]
    status = ('nonprimitive' if max(contents)>1 else
              'obstructed' if any(root_count(p)==p for p in small) else 'admissible')
    return dict(path=path,Q=Q,a=a,forms=forms,contents=contents,determinants=dets,
                E=prod(A for A,_ in forms)*prod(dets),exceptional_roots={p:root_count(p) for p in bad},
                status=status)

if __name__=='__main__':
    record={}
    for r in (1,2,3):
        rows=[branch(w) for d in DIGITS for w in words(r,d)]
        print(r,len(rows),dict(Counter(row['status'] for row in rows)))
        record[r]=rows
    Path(__file__).with_name('branches.json').write_text(json.dumps(record, separators=(',',':'))+'\n')
