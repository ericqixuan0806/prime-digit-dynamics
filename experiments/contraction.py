"""Check the all-orbit inequalities and repeat-state boundary using exact integer arithmetic."""
import json
from verify import check

def main():
    rows, primes = check('million.tsv.gz',10**6)
    def step(p):
        q=rows[p][1][-1]
        return q,(10*p+p%10)//q
    prefixes=0
    for p in primes:
        if p<=23333:
            continue
        q,M,C,n=p,1,0,0
        seen=set()
        while q>=p:
            if q in seen:
                raise ArithmeticError(('new cycle',p))
            seen.add(q)
            s,m=step(q)
            C,M,n=10*C+(q%10)*M,M*m,n+1
            scale=10**n
            if M*s!=scale*p+C:
                raise ArithmeticError(('affine identity',p,n))
            if (p-1)*(M*s)**2 >= (scale*p)**2*(p+2*n-1):
                raise ArithmeticError(('odd spacing',p,n))
            q=s
            prefixes+=1
    q,M=17,1
    for n in range(1,27):
        q,m=step(q)
        M*=m
        if n<26 and M>10**n:
            raise ArithmeticError('earlier crossing for 17')
    if q!=17 or M<=10**26:
        raise ArithmeticError('period obstruction')
    print(json.dumps(dict(prefixes_checked=prefixes,p17_first_crossing=n,p17_at_crossing=q,
                          p17_product_at_crossing=M),indent=2))

if __name__=='__main__':
    main()
