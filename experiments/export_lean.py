"""Export untrusted witness data. All rows are subsequently checked inside Lean."""
import gzip
from math import isqrt
from pathlib import Path
from verify import CYCLE

ROOT=Path(__file__).resolve().parents[1]
def main():
    lines=gzip.decompress((ROOT/'experiments/base.tsv.gz').read_bytes()).decode().splitlines()
    rows=sorted((int(h),int(p),list(map(int,fs.split()))) for p,h,fs in (s.split('\t') for s in lines))
    ix={p:i for i,(_,p,_) in enumerate(rows)}
    data=[f"⟨{p}, {ix[fs[-1]]}, {fs}⟩" for _,p,fs in rows]
    witnesses=[]
    for p in range(23334):
        if p in ix:
            witnesses.append(str(ix[p]))
        elif p < 2:
            witnesses.append('0')
        else:
            witnesses.append(str(next(d for d in range(2,isqrt(p)+1) if p%d==0)))
    source='''import PrimeDynamics.Certificate

/-! Generated witness data from experiments/export_lean.py.
The soundness theorems are independent of this generator. -/
namespace PrimeDynamics.Certificate.Data
set_option maxRecDepth 20000
'''
    # Kernel evaluation of a giant literal Array repeatedly traverses its full spine.
    # A balanced numeric dispatch only evaluates the chosen leaf. Seed witnesses
    # fit in twelve bits; pack sixteen per literal to keep the source small.
    def tree(items, start, width):
        if len(items)==1:
            return items[0]
        mid=len(items)//2
        split=start+mid*width
        return (f"(if i < {split} then {tree(items[:mid],start,width)} "
                f"else {tree(items[mid:],split,width)})")
    def lookup(name, typ, entries, width, default):
        nonlocal source
        parts=[]
        for start in range(0,len(entries),32):
            chunk=entries[start:start+32]
            label=f'{name}Part{len(parts)}'
            source+=f"\nprivate def {label} (i : ℕ) : {typ} :=\n  "+tree(chunk,start*width,width)+"\n"
            parts.append(label+' i')
        source+=(f"\ndef {name} (i : ℕ) : {typ} :=\n  if i < {len(entries)*width} then "
                 +tree(parts,0,32*width)+f" else {default}\n")
    lookup('row','Row',data,1,'⟨23,0,[]⟩')
    packed=[str(sum(int(w)<<(12*j) for j,w in enumerate(witnesses[i:i+16])))
            for i in range(0,len(witnesses),16)]
    lookup('packedWitness','ℕ',packed,16,'0')
    source+="\ndef witness (p : ℕ) : ℕ := (packedWitness p >>> (12*(p%16))) % 4096\n"
    source+='\nend PrimeDynamics.Certificate.Data\n'
    (ROOT/'PrimeDynamics/CertificateData.lean').write_text(source)
    replay = """import PrimeDynamics.CertificateData
namespace PrimeDynamics.Certificate.Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def checkedCover (p : ℕ) : Bool :=
  if p ≤ 23333 then coverOK row 4096 p (witness p) else true
"""
    for label, fn, leaf, top in [('rows','(rowOK row)',6,12),('coverage','checkedCover',9,15)]:
        names=[]
        for i in range(0,2**top,2**leaf):
            name=f'{label}_{i}'
            replay+=f'private theorem {name} : block {fn} {i} {leaf} = true := by decide +kernel\n'
            names.append(name)
        while len(names)>1:
            names=[f'(block_join {a} {b})' for a,b in zip(names[::2],names[1::2])]
        replay+=f'theorem {label}_checked : block {fn} 0 {top} = true :=\n  {names[0]}\n\n'
    replay+='end PrimeDynamics.Certificate.Data\n'
    (ROOT/'PrimeDynamics/CertificateReplay.lean').write_text(replay)
    source='''import PrimeDynamics.Certificate
namespace PrimeDynamics
open Certificate
theorem cycle_nodup : cycle.Nodup := by decide
theorem cycle_length : cycle.length = 26 := by decide
'''
    for p in CYCLE:
        fs=rows[ix[p]][2]
        source+=f'theorem cycleEdge{p} : T {p} = {fs[-1]} := edgeOK_sound (fs := {fs}) (by rfl)\n'
    source+='''
theorem cycle_primes : ∀ p ∈ cycle, Nat.Prime p := by
  have h : cycle.all primeOK = true := by rfl
  exact fun p hp => primeOK_sound (List.all_eq_true.mp h p hp)
end PrimeDynamics
'''
    (ROOT/'PrimeDynamics/Cycle.lean').write_text(source)

if __name__=='__main__':
    main()
