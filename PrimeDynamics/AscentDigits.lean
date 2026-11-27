import PrimeDynamics.RecordProducts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

namespace PrimeDynamics

private theorem not_dvd_small {p a : ℕ} (hp : p.Prime) (small : a < p) (nonunit : 1 < a) :
    ¬ a ∣ p := by
  intro divides
  rcases (Nat.dvd_prime hp).mp divides with h | h <;> omega

/-- A pure outgoing edge at terminal digits 1 or 7 forces a factor 3 at
    the next extension. On a high orbit this factor belongs to its cofactor. -/
theorem pure_ascent_forces_three {p : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (digits : lastDigit p = 1 ∨ lastDigit p = 7)
    (unit : cofactor p 0 = 1) (high : 3 < state p 2) : 3 ∣ cofactor p 1 := by
  have fs := step_factor hp 0
  rw [unit,one_mul] at fs
  change state p 1 = digitExtend p at fs
  have h0 := not_dvd_small (a := 3) hp (by omega) (by decide)
  have qprime : (state p 1).Prime := iterate_prime hp 1
  have qbig : 3 < state p 1 := by
    rw [fs]; unfold digitExtend; omega
  have h1 := not_dvd_small qprime qbig (by decide)
  have ext : 3 ∣ digitExtend (state p 1) := by
    rw [Nat.dvd_iff_mod_eq_zero] at h0 h1 ⊢
    have mod3 (w : ℕ) : digitExtend w % 3 = (w%3+(lastDigit w)%3)%3 := by
      simp [digitExtend,Nat.add_mod,Nat.mul_mod]
    have d1 : lastDigit (state p 1) = lastDigit p := by rw [fs]; simp [lastDigit,digitExtend,Nat.add_mod]
    have hqmod : state p 1 % 3 = (p%3+(lastDigit p)%3)%3 := fs ▸ mod3 p
    rw [mod3,d1]
    rcases (show p%3=1 ∨ p%3=2 by omega) with r | r <;>
      rcases digits with d | d <;> norm_num [r,d] at hqmod ⊢ <;> omega
  rw [← step_factor hp 1] at ext
  rcases Nat.prime_three.dvd_mul.mp ext with a | b
  · exact a
  · exact (not_dvd_small (iterate_prime hp 2) high (by decide) b).elim

def threeWeight (m : ℕ) := if m=3 then 1 else if m=9 then 2 else 0
def sevenWeight (m : ℕ) := if m=7 then 1 else 0
def digitPhase (d : ℕ) := if d=3 then 2 else if d=9 then 1 else 0

set_option synthInstance.maxSize 1024 in
private theorem phase_table : ∀ d r m : Fin 10,
    (d.val=3 ∨ d.val=7 ∨ d.val=9) → (m.val=1 ∨ m.val=3 ∨ m.val=7 ∨ m.val=9) →
    (m.val*r.val)%10=d.val → ¬ (3 ∣ m.val ∧ 3 ∣ d.val) → ¬ (7 ∣ m.val ∧ 7 ∣ d.val) →
    (r.val=3 ∨ r.val=7 ∨ r.val=9) ∧
    threeWeight m.val+digitPhase d.val=sevenWeight m.val+digitPhase r.val := by decide

/-- The complete finite digit transition rule on the closed class 3,7,9. -/
theorem ascent_digit_step {p q m : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (digit : lastDigit p = 3 ∨ lastDigit p = 7 ∨ lastDigit p = 9)
    (fac : digitExtend p = m*q) (allowed : m=1 ∨ m=3 ∨ m=7 ∨ m=9) :
    (lastDigit q = 3 ∨ lastDigit q = 7 ∨ lastDigit q = 9) ∧
    threeWeight m + digitPhase (lastDigit p) = sevenWeight m + digitPhase (lastDigit q) := by
  have noCommon {l : ℕ} (hl : l.Prime) (lt : l < p) (ht : ¬ l ∣ 10) :
      ¬ (l ∣ m ∧ l ∣ lastDigit p) := by
    rintro ⟨hm,hd⟩
    have both : l ∣ digitExtend p := by rw [fac]; exact dvd_mul_of_dvd_left hm q
    change l ∣ 10*p+lastDigit p at both
    have source := (hl.dvd_mul.mp ((Nat.dvd_add_left hd).mp both)).resolve_left ht
    exact not_dvd_small hp lt hl.one_lt source
  have digitEq : (m*lastDigit q)%10 = lastDigit p := by
    have qmod := congrArg (fun n : ℕ => n%10) fac.symm
    change (m*q)%10=(10*p+p%10)%10 at qmod
    simpa [lastDigit,Nat.mul_mod,Nat.add_mod] using qmod
  exact phase_table ⟨lastDigit p,Nat.mod_lt _ (by decide)⟩
    ⟨lastDigit q,Nat.mod_lt _ (by decide)⟩ ⟨m,by omega⟩ digit allowed digitEq
    (noCommon Nat.prime_three (by omega) (by decide))
    (noCommon (by decide : Nat.Prime 7) (by omega) (by decide))

def ascentCount (weight : ℕ → ℕ) (p n : ℕ) := ∑ i ∈ range n, weight (cofactor p i)

/-- On every finite strictly increasing segment starting in the closed digit
    class, the two exponents differ by an endpoint term of absolute value at most two. -/
theorem ascent_exponent_balance {p : ℕ} (hp : p.Prime) (large : 11 ≤ p) (n : ℕ)
    (start : lastDigit p = 3 ∨ lastDigit p = 7 ∨ lastDigit p = 9)
    (up : ∀ i < n, state p i < state p (i+1)) :
    (lastDigit (state p n) = 3 ∨ lastDigit (state p n) = 7 ∨ lastDigit (state p n) = 9) ∧
    ascentCount threeWeight p n + digitPhase (lastDigit p) =
      ascentCount sevenWeight p n + digitPhase (lastDigit (state p n)) ∧
    M p n = 3^(ascentCount threeWeight p n)*7^(ascentCount sevenWeight p n) := by
  induction n with
  | zero => simpa [ascentCount,M,state] using start
  | succ n ih =>
    obtain ⟨digit,balance,word⟩ := ih (fun i hi => up i (by omega))
    have climb (k : ℕ) (hk : k ≤ n) : p ≤ state p k := by
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact (ih (by omega)).trans (up k (by omega)).le
    have next := up n (by omega)
    have stateStep : T (state p n) = state p (n+1) := (Function.iterate_succ_apply' T n p).symm
    obtain ⟨_,m,mem,fac⟩ := (ascent_iff (iterate_prime hp n) (large.trans (climb n le_rfl))).mp
      ⟨stateStep,next⟩
    have factor : cofactor p n = m := Nat.eq_of_mul_eq_mul_right (iterate_prime hp (n+1)).pos
      ((step_factor hp n).trans fac)
    have allowed : m=1 ∨ m=3 ∨ m=7 ∨ m=9 := by simpa using mem
    obtain ⟨newdigit,delta⟩ := ascent_digit_step (iterate_prime hp n) (large.trans (climb n le_rfl))
      digit fac allowed
    change threeWeight m + digitPhase (lastDigit (state p n)) =
      sevenWeight m + digitPhase (lastDigit (state p (n+1))) at delta
    have decomp : m = 3^(threeWeight m)*7^(sevenWeight m) := by
      rcases allowed with rfl | rfl | rfl | rfl <;> decide
    refine ⟨newdigit,?_,?_⟩
    · simp only [ascentCount] at balance ⊢
      rw [sum_range_succ,sum_range_succ,factor]
      omega
    · rw [M,word,factor]
      simp only [ascentCount,sum_range_succ,factor,pow_add]
      conv_lhs => rhs; rw [decomp]
      ring

end PrimeDynamics
