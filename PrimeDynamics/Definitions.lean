import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace PrimeDynamics

def lastDigit (p : ℕ) := p % 10
def digitExtend (p : ℕ) := 10 * p + lastDigit p

def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : 1 < n then n.primeFactors.max' (Nat.nonempty_primeFactors.mpr h) else 0

def T (p : ℕ) := largestPrimeFactor (digitExtend p)

theorem largestPrimeFactor_mem {n : ℕ} (h : 1 < n) :
    largestPrimeFactor n ∈ n.primeFactors := by
  simpa [largestPrimeFactor, h] using n.primeFactors.max'_mem (Nat.nonempty_primeFactors.mpr h)

theorem le_largestPrimeFactor {n q : ℕ} (hn : 1 < n) (hq : q.Prime) (hd : q ∣ n) :
    q ≤ largestPrimeFactor n := by
  simpa [largestPrimeFactor, hn] using n.primeFactors.le_max' q
    (Nat.mem_primeFactors.mpr ⟨hq, hd, by omega⟩)

theorem extend_gt_one {p : ℕ} (hp : 0 < p) : 1 < digitExtend p := by
  unfold digitExtend
  omega

theorem T_prime {p : ℕ} (hp : 0 < p) : (T p).Prime :=
  Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem (extend_gt_one hp))

theorem T_dvd {p : ℕ} (hp : 0 < p) : T p ∣ digitExtend p :=
  Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem (extend_gt_one hp))

def cycle : List ℕ :=
  [23,233,2333,23333,661,601,6011,6679,997,907,313,241,2411,
   47,53,41,137,17,59,599,857,953,9533,13619,19457,821]

def Reaches (p : ℕ) : Prop := ∃ k : ℕ, T^[k] p ∈ cycle
def FiniteDescent : Prop := ∀ p : ℕ, p.Prime → 23333 < p → ∃ k : ℕ, 0 < k ∧ T^[k] p < p
def GlobalAttraction : Prop := ∀ p : ℕ, p.Prime → Reaches p
def FiniteBase : Prop := ∀ p : ℕ, p.Prime → p ≤ 23333 → Reaches p

theorem iterate_prime {p : ℕ} (hp : p.Prime) (n : ℕ) : (T^[n] p).Prime := by
  induction n with
  | zero => exact hp
  | succ n ih => rw [Function.iterate_succ_apply']; exact T_prime ih.pos

theorem reaches_predecessor {p q : ℕ} (h : T p = q) (hq : Reaches q) : Reaches p := by
  obtain ⟨k, hk⟩ := hq
  exact ⟨k+1, by simpa [Function.iterate_succ_apply, h] using hk⟩

theorem finiteDescent_iff_globalAttraction_of_base (base : FiniteBase) :
    FiniteDescent ↔ GlobalAttraction := by
  constructor
  · intro g p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      intro hp
      by_cases hsmall : p ≤ 23333
      · exact base p hp hsmall
      obtain ⟨k, _, hk⟩ := g p hp (by omega)
      obtain ⟨j, hj⟩ := ih _ hk (iterate_prime hp k)
      exact ⟨j+k, by simpa [Function.iterate_add_apply] using hj⟩
  · intro c p hp hlarge
    obtain ⟨k, hk⟩ := c p hp
    have hmax : ∀ q ∈ cycle, q ≤ 23333 := by decide
    have hlt := lt_of_le_of_lt (hmax _ hk) hlarge
    refine ⟨k, ?_, hlt⟩
    cases k with
    | zero => exact (Nat.lt_irrefl _ hlt).elim
    | succ k => omega

end PrimeDynamics
