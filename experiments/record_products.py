"""Exact checks for record products, inverse edges, and cycles with pure runs."""
from collections import Counter
from fractions import Fraction
from math import isqrt, prod
import json

from verify import CYCLE, check, require


def suffix_minima(path):
    indices = []
    for i in reversed(range(len(path))):
        if not indices or path[i] < path[indices[-1]]:
            indices.append(i)
    return indices[::-1]


def exact_root(n, degree):
    if n == 1 or degree == 1:
        return n
    lo, hi = 1, 1 << ((n.bit_length()+degree-1)//degree)
    while lo < hi:
        mid = (lo+hi)//2
        if mid**degree < n:
            lo = mid+1
        else:
            hi = mid
    return lo if lo**degree == n else None


def audit_excess(path, factors, excess, stats, examples):
    source, target = path[0], path[-1]
    t = len(path)-1
    scale = 10**t
    require((excess*target-source) % 10 == 0 and
            excess*target >= scale*(source-target) + source%10*(scale//10),
            ('digit and height', path, excess))
    if excess == 1:
        require(source % 10 == target % 10 and target > 10*scale, ('minimal excess', path))
        stats[f'unit_excess_length_{t}'] += 1
    for g in range(1,t+1):
        if t % g or (g == 1 and excess != 1):
            continue
        s = exact_root(excess,g)
        if s is None:
            continue
        a = 10**(t//g)
        witnesses = []
        for x,y in zip(path,path[1:]):
            for q in set(factors[x][:-1]):
                residue = a*pow(s,-1,q) % q
                if pow(residue,g,q) == q-1 and all(pow(residue,i,q) != 1 for i in range(1,2*g)):
                    require(q <= y and (q-1) % (2*g) == 0, ('primitive edge',x,y,q,g))
                    witnesses.append((q,x,y))
        require(witnesses, ('missing primitive divisor', path, excess, g))
        stats[f'primitive_witness_degree_{g}'] += 1
        key = f'unit_length_{t}' if excess == 1 else f'power_degree_{g}'
        if key not in examples or (excess == 1 and g > examples[key]['degree']):
            q,x,y = min(witnesses)
            examples[key] = {'path':path,'excess':excess,'degree':g,'root':s,
                             'prime':q,'edge':[x,y]}


def record_path(path, factors, totals, worst, power_stats, examples):
    indices = suffix_minima(path)
    require(indices[0] == 0, ('initial minimum', path))
    product_ratio = Fraction(1)
    word_product = 1
    for k, (lo, hi) in enumerate(zip(indices, indices[1:]), 1):
        a = path[lo]
        first = prod(factors[a][:-1])
        product_ratio *= first
        word_product *= first
        totals['minimum_transitions'] += 1
        record = path[lo + 1]
        block = 1
        length = 0
        blocks = 0
        for i in range(lo + 1, hi):
            m = prod(factors[path[i]][:-1])
            block *= m
            word_product *= m
            length += 1
            if path[i + 1] < record:
                excess = block - 10**length
                require(excess > 0, ('record gap', path, i))
                segment = path[i+1-length:i+2]
                audit_excess(segment, factors, excess, power_stats, examples)
                ratio = Fraction(excess, 10**length)
                if worst[0] is None or ratio < worst[0]:
                    worst[:] = [ratio, path[i + 1 - length:i + 2]]
                product_ratio *= 1 + ratio
                totals['descending_records'] += 1
                blocks += 1
                record = path[i + 1]
                block, length = 1, 0
        require(record == path[hi] and length == 0, 'partition missed the minimum')
        totals['excursions_with_multiple_records'] += int(blocks >= 2)
        require(product_ratio * Fraction(path[hi], 10**k)
                == Fraction(word_product * path[hi], 10**hi), ('endpoint', path, hi))
    if len(indices) > 1:
        direct = prod((Fraction(10*a + a % 10, 10*a) for a in path[:-1]), start=Fraction(path[0]))
        require(direct == product_ratio * Fraction(path[-1], 10**(len(indices) - 1)),
                ('digit correction', path))


def compressed_cycle(factors):
    after = [i for i in range(len(CYCLE)) if len(factors[CYCLE[i-1]]) > 1]
    product_ratio = Fraction(1)
    rows = []
    for j, i in enumerate(after):
        length = (after[(j+1) % len(after)]-i) % len(CYCLE) or len(CYCLE)
        a = CYCLE[i]
        q = CYCLE[(i+length) % len(CYCLE)]
        last = CYCLE[(i+length-1) % len(CYCLE)]
        m = prod(factors[last][:-1])
        numerator = 10**length*a + a % 10 * ((10**length-1)//9)
        require(m*q == numerator, ('pure run', i))
        product_ratio *= Fraction(numerator, 10**length*a)
        rows.append([a, length, m, q])
    M = prod(prod(factors[x][:-1]) for x in CYCLE)
    require(product_ratio == Fraction(M, 10**len(CYCLE)) and M % 10 == 1, 'cyclic correction')
    require(1 < product_ratio < (1 + Fraction(1,min(CYCLE)))**len(after), 'cyclic bound')
    return {'period': len(CYCLE), 'reductions':len(after), 'M':M, 'blocks_start_length_cofactor_end':rows}


def repeated_words(factors):
    checked = Counter()
    for p in factors:
        path = [p]
        letters = []
        for _ in range(9):
            a = path[-1]
            fs = factors[a]
            letters.append((a % 10, prod(fs[:-1])))
            path.append(fs[-1])
        for h in (1, 2, 3):
            word = letters[:h]
            M = prod(m for _, m in word)
            if M == 1:
                continue
            for k in (2, 3):
                if letters[(k-1)*h:k*h] != word:
                    break
                first = path[h] - path[0]
                last = path[k*h] - path[(k-1)*h]
                require(M**(k-1)*last == 10**(h*(k-1))*first and first % M**(k-1) == 0,
                        ('repeated full word', p, h, k))
                checked[f'length_{h}_copies_{k}'] += 1
    require(factors[30781] == (7,43973) and factors[43973] == (7,62819)
            and (43973-30781) % 7 == 4, 'changing units digit')
    return dict(sorted(checked.items()))


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def main():
    rows, seeds = check('million.tsv.gz', 10**6)
    factors = {p: fs for p, (_, fs) in rows.items()}
    parents = {}
    for a, fs in factors.items():
        q = fs[-1]
        m = prod(fs[:-1])
        digit = (91*m*q) % 100
        require(digit == a % 10 and (m*q-digit)//10 == a and all(l <= q for l in fs[:-1]),
                ('inverse word', a))
        if a >= 11 and a < q:
            require(q not in parents, ('two smaller prime parents', q, a, parents.get(q)))
            parents[q] = a
    totals = Counter()
    least = [None, None]
    power_stats = Counter()
    examples = {}
    for seed in seeds:
        if seed <= 23333:
            continue
        path = [seed]
        while factors[path[-1]][-1] >= seed:
            path.append(factors[path[-1]][-1])
        totals['first_descent_prefixes'] += 1
        record_path(path, factors, totals, least, power_stats, examples)
    forbidden = []
    for l in range(7, 201):
        if not prime(l):
            continue
        for i in range(1, l):
            if 2*pow(10, i, l) % l == 1:
                require(all(((9+d)*pow(10,j,l)-d) % l == 0 for d,j in ((9,i),(3,2*i))),
                        ('forbidden divisor', l))
                forbidden.append([l,i])
                break
    relaxed = []
    for n in (3, 8, 17, 19):
        p = (10**n-1)//9
        word = [1]*(n-1) + [10**n+1]
        x = p
        for m in word:
            x, rem = divmod(10*x+x%10,m)
            require(rem == 0 and x % 10 == 1, ('relaxed orbit', n))
        require(x == p and prod(word) - 10**n == 1, ('relaxed close', n))
        even_length = n if n % 2 == 0 else n+1
        require(((10**even_length-1)//9) % 11 == 0, 'composite interior repunit')
        relaxed.append({'period':n,'least_state':p,'repunit_length_with_factor_11':even_length})
    print(json.dumps({'verified_graph_edges':len(rows),'distinct_targets_with_smaller_prime_parent_ge11':len(parents),
                      'finite_suffix_records':dict(sorted(totals.items())),
                      'smallest_normalized_record_excess_seen':{'fraction':str(least[0]),'path':least[1]},
                      'record_power_excess':dict(sorted(power_stats.items())),
                      'primitive_divisor_examples':dict(sorted(examples.items())),
                      'repeated_full_words':repeated_words(factors),
                      'repetition_without_digit_match':[30781,43973,62819],
                      'true_cycle':compressed_cycle(factors),'forbidden_prime_and_exponent_up_to_200':forbidden,
                      'integer_relaxation_examples':relaxed},indent=2))


if __name__ == '__main__':
    main()
