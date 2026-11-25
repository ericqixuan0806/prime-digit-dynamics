"""Cross-check the potential inequality and consecutive-record identity using rational arithmetic."""
from fractions import Fraction
from functools import cache
from collections import Counter
import json
from verify import check

@cache
def weight(q):
    if q<=9:
        raise ValueError(q)
    return Fraction(1,q-9)

def main():
    graph,seeds=check('million.tsv.gz',10**6)
    result=Counter()
    for a,(_,fs) in graph.items():
        q=fs[-1]
        if min(a,q)<=9:
            result['edges_outside_shift_domain']+=1
            continue
        if a==q:
            raise ArithmeticError(('fixed point',a))
        if q<a and 11*q>10*a+9:
            raise ArithmeticError(('bad slope',a,q))
        exceptional=weight(a) if a<q else 0
        if 11*weight(a)>10*weight(q)+11*exceptional:
            raise ArithmeticError(('local budget',a,q))
        result['eligible_edges']+=1
    for p in seeds:
        if p<=23333:
            continue
        a=record=p
        total=rises=Fraction(0)
        gain=Fraction(1)
        cost=power=1
        while a>=p:
            q=graph[a][1][-1]
            if q<=9:
                result['prefixes_ending_outside_domain']+=1
                break
            total+=weight(a)
            if q>a:
                rises+=weight(a)
            if total+10*weight(p)>10*weight(q)+11*rises:
                raise ArithmeticError(('prefix budget',p,q))
            result['eligible_prefixes']+=1
            m=(10*a+a%10)//q
            gain*=Fraction(10*a+a%10,10*a)
            cost*=m
            power*=10
            if q>record:
                if Fraction(cost*q,power*record)!=gain:
                    raise ArithmeticError(('record block',p,record,q))
                result['record_blocks']+=1
                record=q
                cost=power=1
                gain=Fraction(1)
            a=q
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__=='__main__':
    main()
