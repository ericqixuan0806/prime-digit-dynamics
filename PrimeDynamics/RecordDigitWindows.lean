import PrimeDynamics.TransferDigits

open Nat

namespace PrimeDynamics

/-- A record of length at least two, with no cofactor divisible by three,
    cannot start at digit seven. At digit one its first cofactor must be seven. -/
theorem three_free_record_head {p t : ℕ} (hp : p.Prime) (large : 11 ≤ p) (long : 2 ≤ t)
    (above : p ≤ state p 1) (high : 3 < state p 2) (free : ¬ 3 ∣ M p t) :
    lastDigit p ≠ 7 ∧ (lastDigit p = 1 → cofactor p 0 = 7) := by
  have ne : state p 1 ≠ p := by simpa [state] using no_fixed_point hp
  obtain ⟨_,m,mem,fac⟩ := (ascent_iff hp large).mp
    (show T p = state p 1 ∧ p < state p 1 from ⟨rfl,lt_of_le_of_ne above ne.symm⟩)
  have actual : cofactor p 0 = m := Nat.eq_of_mul_eq_mul_right (iterate_prime hp 1).pos
    ((step_factor hp 0).trans fac)
  have freeAt (i : ℕ) (hi : i < t) (hit : 3 ∣ cofactor p i) : False :=
    free (hit.trans (cofactor_dvd_word p hi))
  have first : ¬ 3 ∣ m := by rw [← actual]; exact freeAt 0 (by omega)
  have opts : m=1 ∨ m=3 ∨ m=7 ∨ m=9 := by simpa using mem
  have at17 (digit : lastDigit p=1 ∨ lastDigit p=7) : m=7 := by
    have nonunit (h : m=1) := freeAt 1 (by omega)
      (pure_ascent_forces_three hp large digit (actual.trans h) high)
    rcases opts with h | h | h | h
    · exact (nonunit h).elim
    · exact (first (by rw [h])).elim
    · exact h
    · exact (first (h ▸ (by decide : 3 ∣ 9))).elim
  refine ⟨?_,fun digit => actual.trans (at17 (Or.inl digit))⟩
  intro seven
  have hit : 7 ∣ digitExtend p := by rw [fac,at17 (Or.inr seven)]; exact dvd_mul_right _ _
  change 7 ∣ 10*p+lastDigit p at hit
  rw [seven] at hit
  have divides : 7 ∣ p := (show Nat.Prime 7 by decide).dvd_mul.mp
    ((Nat.dvd_add_left (dvd_refl 7)).mp hit) |>.resolve_left (by decide)
  rcases (Nat.dvd_prime hp).mp divides with h | h <;> omega

/-- A long record from digit seven pays a factor three in one of its first two edges. -/
theorem seven_head_early_three {p : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (above : p ≤ state p 1) (high : 3 < state p 2) (seven : lastDigit p=7) :
    3 ∣ cofactor p 0 ∨ 3 ∣ cofactor p 1 := by
  by_contra no
  have free : ¬ 3 ∣ M p 2 := by
    simpa [M,Nat.prime_three.dvd_mul] using no
  exact (three_free_record_head (t := 2) hp large le_rfl above high free).1 seven

/-- Multiplication by either generator of the units modulo ten visits seven
    among any four successive digits. Only the first three transports are needed. -/
theorem four_record_digits {c a b d f : ℕ} (generator : c=3 ∨ c=7)
    (unit : a=1 ∨ a=3 ∨ a=7 ∨ a=9) (hb : b<10) (hd : d<10) (hf : f<10)
    (ab : (c*b)%10=a) (bd : (c*d)%10=b) (df : (c*f)%10=d) :
    a=7 ∨ b=7 ∨ d=7 ∨ f=7 := by
  rcases generator with rfl | rfl <;> rcases unit with rfl | rfl | rfl | rfl <;> omega

/-- Four actual long record words, joined by bridges preserving the last digit,
    have a factor three in the fourth when the first three are free of three
    and have the same generator as their product residue modulo ten. -/
theorem four_record_class_obstruction (p t : ℕ → ℕ) {c : ℕ} (generator : c=3 ∨ c=7)
    (prime : ∀ i < 4, (p i).Prime) (large : ∀ i < 4, 11 ≤ p i)
    (long : ∀ i < 4, 2 ≤ t i) (above : ∀ i < 4, p i ≤ state (p i) 1)
    (high : ∀ i < 4, 3 < state (p i) 2)
    (bridge : ∀ i < 3, lastDigit (state (p i) (t i)) = lastDigit (p (i+1))) :
    (∀ i < 3, (M (p i) (t i))%10=c ∧ ¬ 3 ∣ M (p i) (t i)) →
      lastDigit (p 3)=7 ∧ (3 ∣ cofactor (p 3) 0 ∨ 3 ∣ cofactor (p 3) 1) := by
  intro all
  have no (i : ℕ) (hi : i<3) := (three_free_record_head (prime i (by omega))
    (large i (by omega)) (long i (by omega)) (above i (by omega)) (high i (by omega)) (all i hi).2).1
  have transport (i : ℕ) (hi : i<3) : (c*lastDigit (p (i+1)))%10=lastDigit (p i) := by
    rw [← bridge i hi]
    have dig := product_last_digit (prime i (by omega)) (t i)
    have modc : M (p i) (t i) ≡ c [MOD 10] := (all i (by omega)).1.trans
      (Nat.mod_eq_of_lt (show c<10 by omega)).symm
    have both := (modc.mul_right (state (p i) (t i))).symm
    change (c*state (p i) (t i))%10 = (M (p i) (t i)*state (p i) (t i))%10 at both
    simpa [lastDigit,Nat.mul_mod] using both.trans dig
  have valid : lastDigit (p 0)=1 ∨ lastDigit (p 0)=3 ∨ lastDigit (p 0)=7 ∨ lastDigit (p 0)=9 := by
    have cop (a : ℕ) (lo : 1<a) (hi : a<p 0) : p 0%a ≠ 0 := by
      intro h
      rcases (Nat.dvd_prime (prime 0 (by decide))).mp (Nat.dvd_iff_mod_eq_zero.mpr h) with k | k <;> omega
    have big := large 0 (by decide)
    have odd := cop 2 (by decide) (by omega)
    have five := cop 5 (by decide) (by omega)
    unfold lastDigit
    omega
  have seven := four_record_digits generator valid
    (Nat.mod_lt (p 1) (by decide : 0<10)) (Nat.mod_lt (p 2) (by decide : 0<10))
    (Nat.mod_lt (p 3) (by decide : 0<10)) (transport 0 (by decide))
    (transport 1 (by decide)) (transport 2 (by decide))
  have fourth : lastDigit (p 3)=7 := by
    rcases seven with h | h | h | h
    · exact (no 0 (by decide) h).elim
    · exact (no 1 (by decide) h).elim
    · exact (no 2 (by decide) h).elim
    · exact h
  exact ⟨fourth,seven_head_early_three (prime 3 (by decide)) (large 3 (by decide))
    (above 3 (by decide)) (high 3 (by decide)) fourth⟩

end PrimeDynamics
