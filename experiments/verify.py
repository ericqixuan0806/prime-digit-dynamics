"""Independent Python standard-library checker. A row is p, distance, sorted factors of D(p)."""
import gzip
import json
from collections import Counter
from functools import cache
from math import isqrt, prod
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CYCLE = (23,233,2333,23333,661,601,6011,6679,997,907,313,241,2411,
         47,53,41,137,17,59,599,857,953,9533,13619,19457,821)

def require(ok, what):
    if not ok:
        raise ValueError(str(what))

def prime_sieve(bound):
    a = bytearray(b'\1') * (bound + 1)
    a[:2] = b'\0\0'
    for i in range(2, isqrt(bound) + 1):
        if a[i]:
            a[i*i::i] = bytes((bound - i*i)//i+1)
    return a

def check(name, bound):
    rows = {}
    for line in gzip.decompress((ROOT / name).read_bytes()).decode('ascii').splitlines():
        ps, rs, fs = line.split('\t')
        p, rank = int(ps), int(rs)
        factors = tuple(map(int, fs.split()))
        require(p not in rows and rank >= 0 and factors and factors == tuple(sorted(factors)), line)
        rows[p] = rank, factors
    sieve = prime_sieve(max(bound, isqrt(max(max(p, *fs) for p, (_,fs) in rows.items()))))
    trial = [i for i,x in enumerate(sieve) if x]
    @cache
    def prime(p):
        if p < len(sieve):
            return p >= 2 and bool(sieve[p])
        for q in trial:
            if q*q > p:
                break
            if p % q == 0:
                return False
        return True
    require(len(set(CYCLE)) == len(CYCLE) == 26 and max(CYCLE) == 23333, 'cycle metadata')
    require({p for p,(h,_) in rows.items() if h==0} == set(CYCLE), 'cycle labels')
    for p, (rank, fs) in rows.items():
        require(prime(p) and all(map(prime,fs)) and prod(fs)==10*p+p%10, ('factorization',p,fs))
        q = fs[-1]
        require(q in rows, ('missing successor',q))
        if rank:
            require(rows[q][0]+1 == rank, ('rank',p))
        else:
            require(q == CYCLE[(CYCLE.index(p)+1)%26], ('cycle edge',p))
    seeds = [p for p in range(2,bound+1) if sieve[p]]
    require(all(p in rows for p in seeds), 'seed missing')
    # Also guard the claimed extent of the graph: every extra row is reached.
    reached = set(CYCLE)
    for seed in seeds:
        p = seed
        while p not in reached:
            reached.add(p)
            p = rows[p][1][-1]
    require(reached == set(rows), 'extraneous row')
    return rows, seeds

def main():
    base, small = check('base.tsv.gz',23333)
    rows, seeds = check('million.tsv.gz',10**6)
    require(all(rows[p] == row for p,row in base.items()), 'base disagrees')
    nxt = {p:fs[-1] for p,(_,fs) in rows.items()}
    first, multipliers, rising = Counter(), Counter(), Counter()
    slowest, max_time, crossings, mismatches = [], 0, 0, []
    for p in seeds:
        if p <= 10**5:
            q = p
            for j in range(1,4):
                if nxt[q] <= q:
                    break
                rising[j] += 1
                q = nxt[q]
        if p <= 23333:
            continue
        if nxt[p] > p:
            multipliers[(10*p+p%10)//nxt[p]] += 1
        k, q, m_product, first_crossing = 0, p, 1, None
        while q >= p:
            m_product *= (10*q+q%10)//nxt[q]
            q, k = nxt[q], k+1
            if first_crossing is None and m_product > 10**k:
                first_crossing = k
        require(first_crossing is not None, ('descent without crossing',p))
        if p > 9 * first_crossing * 10**(first_crossing-1):
            crossings += 1
            require(k == first_crossing, ('crossing theorem',p))
        if k != first_crossing:
            mismatches.append([p,first_crossing,k])
        first[k] += 1
        if k > max_time:
            slowest, max_time = [], k
        if k == max_time:
            slowest.append(p)
    sample = [54059]
    while sample[-1] >= sample[0]:
        sample.append(nxt[sample[-1]])
    stats = dict(base_primes=len(small), base_rows=len(base), million_primes=len(seeds),
                 million_rows=len(rows), high_seeds=sum(first.values()), first_descent=dict(sorted(first.items())),
                 ascending_cofactor=dict(sorted(multipliers.items())), A_at_100000=dict(sorted(rising.items())),
                 max_first_descent=max_time, slowest=slowest, example=sample,
                 max_prime=max(rows), max_extended=max(10*p+p%10 for p in rows),
                 above_crossing_threshold=crossings, empirical_crossing_mismatches=len(mismatches),
                 mismatch_examples=mismatches[:10], base_max_prime=max(base), base_max_rank=max(h for h,_ in base.values()))
    print(json.dumps(stats, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
