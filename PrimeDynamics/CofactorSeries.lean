import PrimeDynamics.OrbitContraction
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp

namespace PrimeDynamics

/-- Finite digit-weighted sum of the normalized prefix cofactor products. -/
def correctionSum (p : ℕ) : ℕ → ℚ
  | 0 => 0
  | i+1 => correctionSum p i + (lastDigit (state p i) : ℚ) * (M p i : ℚ) / (10:ℚ)^(i+1)

theorem correction_sum_eq (p n : ℕ) :
    (C p n : ℚ) / (10:ℚ)^n = correctionSum p n := by
  induction n with
  | zero => simp [C,correctionSum]
  | succ n ih =>
    rw [correctionSum, ← ih, C, pow_succ]
    push_cast
    field_simp
    ring

theorem normalized_endpoint {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ((M p n * state p n : ℕ):ℚ) / (10:ℚ)^n = (p:ℚ) + correctionSum p n := by
  rw [affine_identity hp n, ← correction_sum_eq]
  push_cast
  field_simp
  ring

end PrimeDynamics
