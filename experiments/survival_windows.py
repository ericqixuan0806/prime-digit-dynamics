"""Exact checks for finite survival, first-descent gaps and adaptive reciprocal sums."""
import json
from collections import Counter
from fractions import Fraction
from functools import cache
from math import gcd, isqrt
from pathlib import Path

from verify import check, require


@cache
def is_prime(n):
    if n < 2 or n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


@cache
def largest_factor(n):
    largest = 1
    d = 2
    while d * d <= n:
        while n % d == 0:
            n //= d
            largest = d
        d += 1
    return max(n, largest)


def words(r, prefix=(), product=1):
    if len(prefix) == r:
        yield prefix
        return
    cap = 11 ** (len(prefix) + 1)
    for m in range(1, cap // product + 1):
        if gcd(m, 10) == 1:
            yield from words(r, prefix + (m,), product * m)


def from_words(bound, r):
    """Enumerate using the final congruence and trial division, with no successor table."""
    found = set()
    count = 0
    for word in words(r):
        count += 1
        for initial_digit in (1, 3, 7, 9):
            digit = initial_digit
            M, C = 1, 0
            for m in word:
                C = 10 * C + digit * M
                M *= m
                digit = digit * pow(m, -1, 10) % 10
            residue = -C * pow(10**r, -1, M) % M
            a = initial_digit + 10 * ((residue - initial_digit) * pow(10, -1, M) % M)
            for seed in range(a, bound + 1, 10 * M):
                if seed < 11 or not is_prime(seed):
                    continue
                state = seed
                for m in word:
                    q, remainder = divmod(10 * state + state % 10, m)
                    require(remainder == 0, ('CRT', seed, word, state))
                    if q < seed or q < largest_factor(m) or not is_prime(q):
                        break
                    state = q
                else:
                    require(seed not in found, ('multiple words', seed, word))
                    found.add(seed)
    return count, found


def finite_tail_minima(path, counts):
    """Use minima of a finite path suffix only; the forward orbit after the path is irrelevant."""
    minima = []
    for i in reversed(range(len(path))):
        if not minima or path[i] < path[minima[-1]]:
            minima.append(i)
    minima.reverse()
    for start, stop in zip(minima, minima[1:]):
        v, s, w = path[start], path[start + 1], path[stop]
        require(v < w <= s, ('suffix minimum order', v, w, s))
        counts['suffix_minimum_transitions'] += 1
        m = (10 * v + v % 10) // s
        if m > 1:
            require(5 * (w + 1) <= 2 * (10 * (v + 1)), ('nontrivial cofactor', v, w, m))
        if w < s:
            t = next(j for j in range(1, stop - start) if path[start + 1 + j] < s)
            counts['proper_excursions'] += 1
            if 18 * 11**t <= s:
                scale = 10 * (v + 1)
                require(8 * 10**t * (scale - w - 1) >= scale, ('excursion loss', v, w, s, t))
                counts['excursions_meeting_size_threshold'] += 1


def block_checks(nxt, seeds, r):
    floor = 18 * 11**r
    K = 2 * r * (10**r + 1)
    counts = Counter()
    for seed in seeds:
        path = [seed]
        seen = {seed}
        while nxt[path[-1]] >= floor and nxt[path[-1]] not in seen:
            path.append(nxt[path[-1]])
            seen.add(path[-1])
        finite_tail_minima(path, counts)
        index = 0
        exceptional = Fraction(0)
        while len(path) - index > r:
            start = path[index]
            for j in range(1, r + 1):
                end = path[index + j]
                if end < start:
                    cost = sum(Fraction(1, v) for v in path[index:index + j])
                    require(cost <= K * (Fraction(1, end) - Fraction(1, start)),
                            ('unpaid descent block', start, j))
                    counts['descent_blocks'] += 1
                    index += j
                    break
            else:
                exceptional += Fraction(1, start)
                index += 1
                counts['survival_steps'] += 1
        total = sum(Fraction(1, v) for v in path[:-1])
        require(total + Fraction(K, seed) <= Fraction(K + r, floor) + (K + 1) * exceptional,
                ('block sum', seed, r))
        counts['segments'] += 1
    return dict(sorted(counts.items()))


def main():
    graph, seeds = check('million.tsv.gz', 10**6)
    nxt = {p: fs[-1] for p, (_, fs) in graph.items()}
    high = [p for p in seeds if p > 23333]
    survivors, increasing, gap = Counter(), Counter(), Counter()
    for p in high:
        a, M, C, j = p, 1, 0, 0
        rising = True
        while a >= p:
            q = nxt[a]
            m = (10 * a + a % 10) // q
            j += 1
            M, C = M * m, 10 * C + a % 10 * M
            require(M * q == 10**j * p + C and C + 9 * 10**j <= 9 * 11**j,
                    ('prefix intercept', p, j))
            rising = rising and q > a
            if q >= p:
                require(M <= 11**j, ('cofactor bound', p, j))
                survivors[j] += 1
                increasing[j] += int(rising)
            else:
                require(M >= 10**j + 1, ('missing excess', p, j))
                if p >= 18 * 11**j:
                    require(2 * (10**j + 1) * (p - q) >= p, ('descent gap', p, j))
                    gap[j] += 1
            a = q
    old = json.loads((Path(__file__).parent / 'statistics.json').read_text())
    horizon = old['max_first_descent']
    for r in range(1, horizon + 1):
        complement = sum(n for j, n in old['first_descent'].items() if int(j) > r)
        require(survivors[r] == complement, ('first-descent distribution', r))
    independent = {}
    for r in (2, 3):
        tested, actual = from_words(10000, r)
        direct = set()
        for p in seeds:
            if 11 <= p <= 10000:
                a = p
                for _ in range(r):
                    a = nxt[a]
                    if a < p:
                        break
                else:
                    direct.add(p)
        require(actual == direct, ('independent enumeration', r, actual ^ direct))
        independent[r] = {'word_count_before_digit_choice': tested, 'surviving_seeds': len(actual)}
    witness = [673273, 23459, 234599, 38459, 384599]
    require(all(nxt[a] == b for a, b in zip(witness, witness[1:])), 'consecutive local minima')
    a, v, peak, w, b = witness
    require(a > v < peak > w < b and v < w, 'valley ordering')
    blocks = {}
    for r in range(1, 5):
        eligible = [p for p in high if p >= 18 * 11**r]
        sample = [eligible[i * len(eligible) // 1024] for i in range(1024)]
        blocks[r] = block_checks(nxt, sample, r)
    print(json.dumps({
        'seed_interval': [23334, 10**6], 'prime_seeds': len(high),
        'survival_and_strict_ascent': [
            {'r': r, 'survival': survivors[r], 'strict_ascent': increasing[r],
             'survival_with_a_nonascending_step': survivors[r] - increasing[r]}
            for r in range(1, horizon + 1)],
        'first_descents_meeting_size_threshold_by_time': dict(sorted(gap.items())),
        'independent_CRT_enumeration_11_through_10000': independent,
        'adaptive_blocks_1024_spaced_seeds_per_horizon': blocks,
        'increasing_consecutive_valleys': {
            'states': witness, 'edge_factor_lists': [graph[q][1] for q in witness[:-1]]}
    }, indent=2))


if __name__ == '__main__':
    main()
