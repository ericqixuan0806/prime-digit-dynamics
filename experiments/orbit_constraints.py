"""Exact record spacing, tail-minimum digit costs and rising-word checks."""
from collections import Counter
from functools import cache
from itertools import product
from math import gcd, isqrt, prod
import json

from record_products import compressed_cycle, suffix_minima
from verify import check, require


def pure_runs(path, factors):
    start = 0
    for i, p in enumerate(path[:-1]):
        word = factors[p][:-1]
        if word:
            yield i+1-start, word, p, path[i+1]
            start = i+1
    require(start == len(path)-1, ('missing final reduction', path))


def record_data(rows):
    @cache
    def record(p):
        path = [p]
        while rows[path[-1]][0] > 0:
            path.append(rows[path[-1]][1][-1])
            if path[-1] < p:
                return tuple(path)
        return ()

    factors = {p: fs for p, (_, fs) in rows.items()}
    three = {}
    long_words = {}
    digit_one_example = None
    seen = Counter()
    pattern = Counter()
    for p in sorted(rows):
        if p < 11:
            continue
        path = record(p)
        if not path:
            continue
        y = path[-1]
        t = len(path)-1
        runs = list(pure_runs(path, factors))
        primes = {q for _, fs, _, _ in runs for q in fs}
        m = prod(prod(fs) for _, fs, _, _ in runs)
        e = m-10**t
        require(e > 0 and runs[-1][1] and prod(runs[-1][1]) >= 11, ('descent',p))
        seen['transient_first_drops'] += 1
        if e <= 11*(p-y):
            require(max(primes) < p, ('large factor',p))
            seen['small_excess_relative_to_gap'] += 1
        if t >= 2 and path[2] > 3:
            long_words[p] = (y, e)
            if m % 3:
                require(p%10 != 7, ('three-free record starts at seven', p))
                seen['long_three_free_heads'] += 1
                if p%10 == 1:
                    require(prod(factors[p][:-1]) == 7, ('forced first seven', p))
                    seen['long_three_free_heads_at_one'] += 1
                    if p > 23333 and digit_one_example is None:
                        digit_one_example = path
        if e != 3:
            continue
        if len(runs) == 1:
            require(all(gcd(m,10**r+3)==1 for r in range(t)), ('single final division',p))
        three[p] = (path, runs, primes)
        pattern[str((t,len(runs)))] += 1
        for h, fs, source, target in runs:
            for q in set(fs):
                require(q < p and q <= target and all(pow(10,d,q) != 1 for d in range(1,h+1)),
                        ('short return',p,q,h))
                seen['order_witnesses_per_distinct_factor_in_edge'] += 1
    evidence = {}
    high_adjacent = {}
    for p, (path, runs, support) in sorted(three.items()):
        t = len(path)-1
        x = path[-1]
        while rows[x][0] > 0:
            if x in three:
                other, more_runs, support2 = three[x]
                t2 = len(other)-1
                shared = support & support2
                key = ('equal_length' if t == t2 else 'different_length') + (
                    '_shared' if shared else '_disjoint')
                seen['ordered_pairs_'+key] += 1
                if x == path[-1] and min(min(path),min(other)) > 23333:
                    seen['adjacent_above_base_'+key] += 1
                    if key not in high_adjacent:
                        high_adjacent[key] = [path,other]
                if key not in evidence:
                    bridge = list(path)
                    while bridge[-1] != x:
                        bridge.append(factors[bridge[-1]][-1])
                    evidence[key] = {'first':path,'second':other,'bridge_from_first_end':bridge[t:],
                                     'shared_primes':sorted(shared)}
                if t != t2:
                    gap = abs(t2-t)
                    for h,fs,_,_ in runs+more_runs:
                        for q in shared.intersection(fs):
                            require(gap > h and pow(10,gap,q)==1, ('spacing',p,x,q))
            x = factors[x][-1]
    forced_examples = {}
    for p in long_words:
        x = p
        starts = []
        excesses = []
        while x in long_words and len(excesses) < 4:
            starts.append(x)
            x, e = long_words[x]
            excesses.append(e)
        if len(excesses) == 4:
            seen['four_adjacent_long_records'] += 1
            for group in ((3, 13), (7, 27)):
                if all(e%30 in group for e in excesses[:3]):
                    paths = [record(start) for start in starts]
                    early = [prod(factors[z][:-1]) for z in paths[-1][:2]]
                    require(starts[-1]%10 == 7 and any(u%3 == 0 for u in early)
                            and excesses[3]%3 == 2 and excesses[3] >= 11,
                            ('forced early factor three', p, excesses))
                    seen['four_adjacent_forced_threes'] += 1
                    forced_examples.setdefault(str(group), {'records': paths, 'excesses': excesses,
                                                             'first_two_cofactors_in_last': early})
    return {'counts':dict(sorted(seen.items())), 'e3_distinct_starts':len(three),
            'e3_length_reductions':dict(sorted(pattern.items())), 'pair_examples':evidence,
            'three_free_digit_one_example':digit_one_example, 'forced_three_examples':forced_examples,
            'adjacent_above_base_examples':high_adjacent}


def check_minimum_windows(rows, seeds):
    counts = Counter()
    for p in seeds:
        if p <= 23333:
            continue
        path = [p]
        while rows[path[-1]][1][-1] >= p:
            path.append(rows[path[-1]][1][-1])
        indices = suffix_minima(path)
        series = []
        for lo,hi in zip(indices,indices[1:]):
            if len(rows[path[lo]][1]) != 1:
                series.clear()
                continue
            if hi == lo+1:
                continue
            head = path[lo+1]
            position = lo+1
            product = 1
            blocks = bad = 0
            for i in range(lo+1,hi):
                product *= prod(rows[path[i]][1][:-1])
                if path[i+1] < head:
                    excess = product-10**(i+1-position)
                    bad += int(excess%30 not in (3,13))
                    blocks += 1
                    product, head, position = 1,path[i+1],i+1
            require(position==hi and blocks>0, ('record partition',p))
            if bad == 0:
                require(path[lo]%10 in (3,9) and pow(3,blocks,10)*path[hi]%10==path[lo]%10,
                        ('ordinary transition',path[lo],path[hi]))
                counts['all_ordinary_transitions'] += 1
            series.append((blocks,bad))
            K = B = 0
            for n,(k,b) in enumerate(reversed(series),1):
                K += k
                B += b
                require(2*n <= K+3*B+2, ('transfer cost',p,n))
                counts['pure_first_subwindows'] += 1
            counts['nonempty_pure_first_transitions'] += 1
    return dict(sorted(counts.items()))


def check_ascent_words(rows):
    phase = {7:0,9:1,3:2}
    counts = Counter()
    for p in rows:
        if p < 11:
            continue
        x = p
        a = b = 0
        while (q := rows[x][1][-1]) > x:
            m = prod(rows[x][1][:-1])
            a += (m==3) + 2*(m==9)
            b += m==7
            require(abs(a-b)<=3, ('initial phase',p,q))
            if p%10 in phase:
                require(q%10 in phase and a-b==phase[q%10]-phase[p%10], ('phase',p,q))
            if m==1 and x%10 in (1,7):
                require(prod(rows[q][1][:-1])%3==0, ('following three',x,q))
            counts['rising_prefixes'] += 1
            counts['max_abs_exponent_difference'] = max(counts['max_abs_exponent_difference'],abs(a-b))
            x = q
    return dict(sorted(counts.items()))


def check_pure_run_stops(rows):
    counts = Counter()
    for p in rows:
        if p < 11:
            continue
        d = p % 10
        x = p
        h = 1
        while len(rows[x][1]) == 1:
            x = rows[x][1][-1]
            h += 1
        q = rows[x][1][-1]
        if d in (1,7):
            require(h <= 2, ('modulo three',p))
        elif (9*p+d) % 7 == 0:
            require(q < x, ('trapped rising candidate',p))
            counts['trapped_starts'] += 1
            counts['longest_pure_prefix_trapped'] = max(counts['longest_pure_prefix_trapped'],h-1)
        else:
            require(h <= 5, ('modulo seven',p,h))
            counts['regular_3_or_9_starts'] += 1
    return dict(sorted(counts.items()))


def single_final_lengths(bound):
    terms = [10**i+3 for i in range(bound+1)]
    admissible = []
    for t in range(1,bound+1):
        old = {r for r in range(t) if gcd(terms[t],terms[r]) > 1}
        returns = {t-h for h in range(1,t+1) if gcd(terms[t],10**h-1) > 1}
        require(old == returns, ('order and earlier lengths',t))
        if not old:
            admissible.append(t)
        if t >= 7 and t % 3 == 1:
            require(old, ('moduli 7 and 13',t))
    return {'bound':bound, 'locally_admissible':admissible,
            'excluded':bound-len(admissible)}


@cache
def prime_divisors(n):
    remaining = n
    result = []
    d = 2
    while d <= isqrt(remaining):
        if remaining % d == 0:
            result.append(d)
            while remaining % d == 0:
                remaining //= d
        d = 3 if d == 2 else d+2
    if remaining > 1:
        result.append(remaining)
    return result


def rising_return_translations():
    table = []
    for divisors,digits in [((3,7),(7,9)), ((9,7,7),(7,3,9))]:
        for lengths in product(range(1,3), *([range(1,6)]*(len(digits)-1))):
            M = 1
            C = 0
            for h,u,d in zip(lengths,divisors,digits):
                C = 10**h*C+M*d*((10**h-1)//9)
                M *= u
            difference = 10**sum(lengths)-M
            q = next(q for q in prime_divisors(difference) if C % q)
            require(difference % q == 0 and gcd(q,M*C) == 1, ('translation',lengths,q))
            table.append({'cofactors':divisors,'lengths':lengths,'intercept':C,'prime':q})
    require(len(table) == 60, 'all return shapes')
    return table


def return_rate_mod13(shapes):
    upper = [0, 1, 1, 0, 0, 0, 0, 1, 2, 0, 2, 2, 0]
    lower = [0, 3, 1, 5, 2, 0, 4, 1, 0, 3, 0, 4, 2]
    edges = set()
    for shape in shapes:
        lengths = tuple(shape['lengths'])
        a = len(lengths)-1
        h = sum(lengths)
        digits = (7, 9) if a == 1 else (7, 3, 9)
        steps = []
        for d, length, u in zip(digits, lengths, shape['cofactors']):
            steps.extend([(d, 1)]*(length-1))
            steps.append((d, u))
        for x in range(1, 13):
            y = x
            for d, u in steps:
                y = (10*y+d)*pow(u, -1, 13) % 13
                if y == 0:
                    break
            else:
                require(2*h+upper[x] <= 13*a+upper[y], ('upper time', x, lengths, y))
                require(11*a+lower[x] <= 7*h+lower[y], ('lower time', x, lengths, y))
                edges.add((x, lengths, y))
    cycles = [
        [(1, (2, 5), 10), (10, (1, 5), 1)],
        [(1, (1, 1), 10), (10, (1, 1, 1), 7),
         (7, (1, 1, 1), 4), (4, (1, 1, 1), 1)],
    ]
    for cycle, numerator, denominator in zip(cycles, (13, 11), (2, 7)):
        require(all(edge in edges for edge in cycle), 'modular equality cycle')
        require(all(edge[2] == cycle[(i+1)%len(cycle)][0] for i, edge in enumerate(cycle)),
                'modular closure')
        h = sum(sum(lengths) for _, lengths, _ in cycle)
        a = sum(len(lengths)-1 for _, lengths, _ in cycle)
        require(denominator*h == numerator*a, 'modular rate')
    return {'modulus': 13, 'edges': len(edges), 'upper_time_potential': upper,
            'lower_time_potential': lower, 'equality_cycles': cycles}


def main():
    rows,seeds = check('million.tsv.gz',10**6)
    factors = {p:fs for p,(_,fs) in rows.items()}
    cyc = compressed_cycle(factors)
    blocks = cyc['blocks_start_length_cofactor_end']
    g = gcd(*(x%10*((10**h-1)//9) for x,h,_,_ in blocks))
    E = cyc['M']-10**cyc['period']
    require(E%g==0, 'cycle divisor')
    shapes = rising_return_translations()
    print(json.dumps({'records':record_data(rows),'minimum_windows':check_minimum_windows(rows,seeds),
                      'ascent':check_ascent_words(rows),'pure_run_stops':check_pure_run_stops(rows),
                      'single_final_lengths':single_final_lengths(256),
                      'return_translations':shapes,'return_rate_mod13':return_rate_mod13(shapes),
                      'known_cycle':{'G':g,'excess':E}},
                     indent=2,sort_keys=True))


if __name__=='__main__':
    main()
