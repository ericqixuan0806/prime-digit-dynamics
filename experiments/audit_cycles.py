"""Independent enumeration by prime exponents, with forward iteration on every eligible seed."""
from itertools import product
from math import prod
import json
from sympy import factorint
from dynamics import T
from verify import check

def allocations(e,n):
    if n==1:
        yield (e,)
    else:
        for j in range(e+1):
            for tail in allocations(e-j,n-1):
                yield (j,)+tail

def run():
    bound=10**6
    check('million.tsv.gz',bound)
    out=[]
    for n in range(1,8):
        N=10**n
        top=(10*bound+9)**n//bound**n
        words=0
        starts=set()
        for M in range(N+1,top+1,10):
            fs=factorint(M)
            powers=[list(allocations(e,n)) for e in fs.values()]
            for dist in product(*powers):
                w=[prod(int(q)**ds[i] for q,ds in zip(fs,dist)) for i in range(n)]
                words+=1
                if w[0]>9:
                    continue
                for d0 in (1,3,7,9):
                    d=d0; den=1; B=0
                    for m in w:
                        B=10*B+d*den
                        den*=m
                        d=next(x for x in (1,3,7,9) if m*x%10==d)
                    p,r=divmod(B,M-N)
                    if not r and p>bound and p%10==d0:
                        starts.add(p)
        # A candidate need not itself be prime. Composite starts may also be checked:
        # all successors are prime, so no composite can return to itself.
        for p in starts:
            q=p
            for _ in range(n):
                q=T(q)
            if p==q:
                raise ArithmeticError(('closed path',p,n))
        out.append(dict(n=n,words=words,distinct_candidate_seeds=len(starts)))
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    run()
