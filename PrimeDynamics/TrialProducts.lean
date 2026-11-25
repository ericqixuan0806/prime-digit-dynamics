import PrimeDynamics.Definitions

namespace PrimeDynamics.TrialProducts

/-- Product of consecutive integers starting at s with length 2^k. -/
def segment (s : ℕ) : ℕ → ℕ
  | 0 => s
  | k+1 => segment s k * segment (s+2^k) k

theorem member_dvd {s k d : ℕ} (lo : s ≤ d) (hi : d < s + 2^k) : d ∣ segment s k := by
  induction k generalizing s with
  | zero =>
    simp only [pow_zero] at hi
    have he : d=s := by omega
    simp [he,segment]
  | succ k ih =>
    rw [pow_succ] at hi
    by_cases h : d < s+2^k
    · exact dvd_mul_of_dvd_left (ih lo h) _
    · exact dvd_mul_of_dvd_right (ih (by omega) (by omega)) _

/-- A coprime factorial rules out every possible small divisor at once. -/
theorem prime_of_coprime {p k multiple : ℕ} (hp : 2 ≤ p) (bound : p < (1+2^k)^2)
    (cert : segment 1 k = multiple) (cop : Nat.gcd p multiple = 1) : p.Prime := by
  refine Nat.prime_def_le_sqrt.mpr ⟨hp, fun d hlo hhi hd => ?_⟩
  have hh : d < 1+2^k := hhi.trans_lt (Nat.sqrt_lt.mpr (by simpa [pow_two] using bound))
  have dvd := Nat.dvd_gcd hd (cert ▸ member_dvd (by omega : 1 ≤ d) hh)
  rw [cop] at dvd
  have := Nat.le_of_dvd (by decide : 0 < 1) dvd
  omega

end PrimeDynamics.TrialProducts
