import PrimeDynamics.Certificate
import Mathlib.Tactic.Linarith

namespace PrimeDynamics

theorem no_fixed_point {p : ℕ} (hp : p.Prime) : T p ≠ p := by
  by_cases hlarge : 11 ≤ p
  · intro eq
    have hd := T_dvd hp.pos
    rw [eq, digitExtend] at hd
    have hmul : p ∣ 10*p := dvd_mul_left _ _
    have hlast : p ∣ lastDigit p := (Nat.dvd_add_right hmul).mp hd
    have hpos : 0 < p % 10 := by
      by_contra! h
      have ht := (Nat.dvd_prime hp).mp (Nat.dvd_iff_mod_eq_zero.mpr (by omega : p % 10 = 0))
      omega
    have hle := Nat.le_of_dvd hpos hlast
    omega
  · have hs : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      interval_cases p <;> norm_num at *
    rcases hs with rfl | rfl | rfl | rfl
    all_goals
      intro h
    · have := Certificate.edgeOK_sound (p := 2) (q := 11) (fs := [2,11]) (by rfl); omega
    · have := Certificate.edgeOK_sound (p := 3) (q := 11) (fs := [3,11]) (by rfl); omega
    · have := Certificate.edgeOK_sound (p := 5) (q := 11) (fs := [5,11]) (by rfl); omega
    · have := Certificate.edgeOK_sound (p := 7) (q := 11) (fs := [7,11]) (by rfl); omega

theorem T_le_of_factorization {p a b : ℕ} (hp : 0 < p) (ha : 0 < a) (hb : 0 < b)
    (h : digitExtend p = a*b) : T p ≤ max a b := by
  have hd := T_dvd hp
  rw [h] at hd
  rcases (T_prime hp).dvd_mul.mp hd with h₁ | h₂
  · exact (Nat.le_of_dvd ha h₁).trans (le_max_left _ _)
  · exact (Nat.le_of_dvd hb h₂).trans (le_max_right _ _)

theorem ascent_iff {p q : ℕ} (hp : p.Prime) (hlarge : 11 ≤ p) :
    (T p = q ∧ p < q) ↔ q.Prime ∧
      ∃ m ∈ ([1,3,7,9] : List ℕ), digitExtend p = m*q := by
  constructor
  · rintro ⟨rfl, hlt⟩
    refine ⟨T_prime hp.pos, ?_⟩
    obtain ⟨m, hm⟩ := T_dvd hp.pos
    have hf : digitExtend p = m*T p := by rwa [Nat.mul_comm]
    have hmle : m < 11 := by
      by_contra! big
      have hh := Nat.mul_le_mul big hlt.le
      have he := Nat.mod_lt p (by decide : 0 < 10)
      unfold digitExtend lastDigit at hf
      nlinarith
    have h2 : p%2 ≠ 0 := by
      intro hh
      have := (Nat.dvd_prime hp).mp (Nat.dvd_iff_mod_eq_zero.mpr hh)
      omega
    have h5 : p%5 ≠ 0 := by
      intro hh
      have := (Nat.dvd_prime hp).mp (Nat.dvd_iff_mod_eq_zero.mpr hh)
      omega
    refine ⟨m, ?_, hf⟩
    unfold digitExtend lastDigit at hf
    interval_cases m <;> simp_all <;> omega
  · rintro ⟨hq,m,hm,he⟩
    have hcases : m=1 ∨ m=3 ∨ m=7 ∨ m=9 := by simpa using hm
    have hmpos : 0 < m := by omega
    have hlt : p < q := by
      by_contra! hh
      have hm9 : m ≤ 9 := by omega
      have hh' := Nat.mul_le_mul hm9 hh
      unfold digitExtend at he
      omega
    refine ⟨le_antisymm ?_ ?_, hlt⟩
    · have h := T_le_of_factorization hp.pos hmpos hq.pos he
      simpa [max_eq_right (by omega : m ≤ q)] using h
    · exact le_largestPrimeFactor (extend_gt_one hp.pos) hq (he ▸ dvd_mul_left _ _)

theorem explicit_descent {k d : ℕ} (hk : 1 ≤ k) (hd : d < 10) :
    T (110*k+d) < 110*k+d := by
  have he : digitExtend (110*k+d) = 11*(100*k+d) := by
    simp [digitExtend, lastDigit, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hd]
    omega
  have hh := T_le_of_factorization (by omega : 0 < 110*k+d) (by decide : 0 < 11)
    (by omega : 0 < 100*k+d) he
  rw [max_eq_right (by omega : 11 ≤ 100*k+d)] at hh
  omega

end PrimeDynamics
