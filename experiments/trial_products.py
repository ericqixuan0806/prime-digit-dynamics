"""Write exact factorial witnesses as small hex limbs. Lean proves each value independently."""
from pathlib import Path
import math

def numeral(n):
 if n.bit_length()<=1024:return hex(n)
 half=((n.bit_length()//2+63)//64)*64
 return f'(({numeral(n>>half)} <<< {half}) + {numeral(n%2**half)})'
s2='''import PrimeDynamics.TrialProducts
/-! Computed factorial constants; each equality is verified by the kernel.
Regenerate using experiments/trial_products.py. -/
namespace PrimeDynamics.TrialProducts
set_option maxHeartbeats 0
set_option maxRecDepth 100000
'''
for k in (4,8,12,16):
 s2+=f'\ndef f{k} : ℕ := {numeral(math.factorial(2**k))}\n'
 s2+=f'theorem f{k}_ok : segment 1 {k} = f{k} := by decide +kernel\n'
s2+='end PrimeDynamics.TrialProducts\n'
(Path(__file__).resolve().parents[1]/'PrimeDynamics/TrialData.lean').write_text(s2)
