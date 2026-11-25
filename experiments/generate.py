"""Build a ranked successor graph for the full base and for the larger regression."""
import gzip
from pathlib import Path
import sys
import sympy
from dynamics import CYCLE, factors

OUT = Path(__file__).resolve().parent
def write_certificate(name, rank):
    data = ''.join(f"{p}\t{rank[p]}\t{' '.join(map(str, factors(p)))}\n"
                   for p in sorted(rank)).encode('ascii')
    (OUT / name).write_bytes(gzip.compress(data, compresslevel=9, mtime=0))

def main():
    print(f"Python {sys.version.split()[0]}, SymPy {sympy.__version__}")
    rank = dict.fromkeys(CYCLE, 0)
    lower = 2
    for bound, filename in [(23333, 'base.tsv.gz'), (10**6, 'million.tsv.gz')]:
        for seed in sympy.primerange(lower, bound + 1):
            trail, visiting = [], set()
            p = int(seed)
            while p not in rank:
                if p in visiting:
                    raise ArithmeticError(f"unlisted cycle from {seed}: {trail}")
                visiting.add(p)
                trail.append(p)
                p = factors(p)[-1]
            for x in reversed(trail):
                rank[x] = rank[p] + 1
                p = x
        write_certificate(filename, rank)
        print(f"{filename}: {len(rank)} certified states")
        lower = bound + 1

if __name__ == '__main__':
    main()
