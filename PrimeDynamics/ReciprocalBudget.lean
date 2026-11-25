import PrimeDynamics.GrowthEdges
import PrimeDynamics.OrbitContraction
import Mathlib.Data.Rat.Cast.Order

namespace PrimeDynamics

/-- A descending edge pays for its starting weight after shifting the state by nine. -/
theorem descending_edge_bound {a : ℕ} (ha : a.Prime) (down : T a < a) :
    11 * T a ≤ 10*a + 9 := by
  obtain ⟨m,he⟩ := T_dvd ha.pos
  have hm : 11 ≤ m := by
    by_contra! small
    have hmul := Nat.mul_le_mul_left (T a) (show m ≤ 10 by omega)
    unfold digitExtend at he
    omega
  have hmul := Nat.mul_le_mul_left (T a) hm
  unfold digitExtend lastDigit at he
  omega

def weight (a : ℕ) : ℚ := 1 / ((a:ℚ)-9)

def risingWeight (a : ℕ) : ℚ := if a < T a then weight a else 0

theorem weight_step {a : ℕ} (ha : a.Prime) (hlo : 9 < a) (hnext : 9 < T a) :
    11 * weight a ≤ 10 * weight (T a) + 11 * risingWeight a := by
  have hpos : 0 < (a:ℚ)-9 := sub_pos.mpr (by exact_mod_cast hlo)
  have hqpos : 0 < (T a:ℚ)-9 := sub_pos.mpr (by exact_mod_cast hnext)
  by_cases h : a < T a
  · simp only [risingWeight,if_pos h]
    have hq : 0 ≤ weight (T a) := (one_div_pos.mpr hqpos).le
    linarith
  · have down : T a < a := lt_of_le_of_ne (by omega) (no_fixed_point ha)
    have hnat := descending_edge_bound ha down
    have hrat : 11 * (T a : ℚ) ≤ 10*(a:ℚ)+9 := by exact_mod_cast hnat
    have frac : (11 : ℚ) / ((a:ℚ)-9) ≤ 10 / ((T a:ℚ)-9) :=
      (div_le_div_iff₀ hpos hqpos).mpr (by linarith)
    simpa [weight,risingWeight,h,← mul_div_assoc] using frac

def orbitSum (f : ℕ → ℚ) (p : ℕ) : ℕ → ℚ
  | 0 => 0
  | i+1 => orbitSum f p i + f (state p i)

/-- Exact telescoping inequality. Repeated states are allowed here. -/
theorem reciprocal_budget {p n : ℕ} (hp : p.Prime) (above : ∀ i ≤ n, 9 < state p i) :
    orbitSum weight p n + 10*weight p ≤ 10*weight (state p n) + 11*orbitSum risingWeight p n := by
  induction n with
  | zero => simp [orbitSum,state]
  | succ n ih =>
    have left := ih (fun i hi => above i (by omega))
    have steq : state p (n+1) = T (state p n) := Function.iterate_succ_apply' T n p
    have right := weight_step (a := state p n) (iterate_prime hp n) (above n (by omega)) (steq ▸ above (n+1) le_rfl)
    simp only [orbitSum]
    rw [← steq] at right
    linarith

end PrimeDynamics
