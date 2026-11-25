import PrimeDynamics.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeDynamics

def state (p i : ℕ) := T^[i] p
def cofactor (p i : ℕ) := digitExtend (state p i) / state p (i+1)

def M (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => M p i * cofactor p i

def C (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => 10 * C p i + lastDigit (state p i) * M p i

theorem step_factor {p : ℕ} (hp : p.Prime) (i : ℕ) :
    cofactor p i * state p (i+1) = digitExtend (state p i) := by
  have h : state p (i+1) = T (state p i) := Function.iterate_succ_apply' T i p
  exact Nat.div_mul_cancel (h ▸ T_dvd (iterate_prime hp i).pos)

theorem affine_identity {p : ℕ} (hp : p.Prime) (i : ℕ) :
    M p i * state p i = 10^i * p + C p i := by
  induction i with
  | zero => simp [M, C, state]
  | succ i ih =>
    calc
      M p (i+1) * state p (i+1) = M p i * digitExtend (state p i) := by
        rw [M, Nat.mul_assoc, step_factor hp]
      _ = 10 * (M p i * state p i) + lastDigit (state p i) * M p i := by
        unfold digitExtend
        ring
      _ = _ := by rw [ih, C, pow_succ]; ring

/-- A division-free bound on the additive error through the first crossing. -/
theorem error_bound (p n : ℕ) (h : ∀ i < n, M p i ≤ 10^i) :
    10 * C p n ≤ 9 * n * 10^n := by
  induction n with
  | zero => simp [C]
  | succ n ih =>
    have hb := ih (fun i hi => h i (by omega))
    have hd : lastDigit (state p n) ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
    have hm := Nat.mul_le_mul hd (h n (by omega))
    rw [C, pow_succ]
    nlinarith

/-- The actual orbit descends when the excess in its cofactor product pays the error bound. -/
theorem first_crossing_descent {p n : ℕ} (hp : p.Prime)
    (hprefix : ∀ i < n, M p i ≤ 10^i)
    (paid : 9 * n * 10^n < 10 * (M p n - 10^n) * p) : state p n < p := by
  have hb := error_bound p n hprefix
  have hi := affine_identity hp n
  have hbig : 10^n ≤ M p n := by
    by_contra! hc
    have hz : M p n - 10^n = 0 := Nat.sub_eq_zero_of_le hc.le
    simp [hz] at paid
  have he : C p n < (M p n - 10^n) * p := by nlinarith
  have hdecomp : (M p n - 10^n) * p + 10^n * p = M p n * p := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hbig]
  by_contra! hh
  have hh' := Nat.mul_le_mul_left (M p n) hh
  omega

theorem no_descent_before_crossing {p i : ℕ} (hp : p.Prime) (hm : M p i ≤ 10^i) :
    p ≤ state p i := by
  by_contra! h
  have hi := affine_identity hp i
  have hpos : 0 < 10^i := by positivity
  have hlt := lt_of_le_of_lt (Nat.mul_le_mul_right (state p i) hm) (Nat.mul_lt_mul_of_pos_left h hpos)
  omega

theorem first_crossing_iff_descent {p n : ℕ} (hp : p.Prime)
    (hprefix : ∀ i < n, M p i ≤ 10^i) (large : 9 * n * 10^n < 10 * p) :
    10^n < M p n ↔ state p n < p := by
  constructor
  · intro h
    apply first_crossing_descent hp hprefix
    have hg : 1 ≤ M p n - 10^n := by omega
    calc
      9 * n * 10^n < 10 * p := large
      _ ≤ 10 * (M p n - 10^n) * p := by
        simpa using Nat.mul_le_mul_right p (Nat.mul_le_mul_left 10 hg)
  · exact fun h => lt_of_not_ge fun hm => (Nat.not_lt.mpr (no_descent_before_crossing hp hm)) h

end PrimeDynamics
