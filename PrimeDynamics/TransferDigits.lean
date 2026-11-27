import PrimeDynamics.AscentDigits
import PrimeDynamics.RecordSpacing

open Finset Nat

namespace PrimeDynamics

/-- Products of positive record lengths whose excess has residue 3 or 13 mod 30. -/
theorem ordinary_record_residues {p t e : ℕ} (length : 0 < t) (excess : M p t = 10^t+e)
    (residue : e%30=3 ∨ e%30=13) : M p t ≡ 3 [MOD 10] ∧ ¬ 3 ∣ M p t := by
  have power (k : ℕ) : 10^(k+1) ≡ 10 [MOD 30] := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ]; exact (ih.mul_right 10).trans (by decide)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt length)
  have joined := (power k).add_right e
  change (10^(k+1)+e)%30 = (10+e)%30 at joined
  rw [excess,Nat.dvd_iff_mod_eq_zero]
  change (10^(k+1)+e)%10 = 3 ∧ (10^(k+1)+e)%3 ≠ 0
  omega

/-- Test ordinary record products on consecutive segments of the actual trajectory. -/
def ordinaryRecordWords (p : ℕ) : List ℕ → Prop
  | [] => True
  | t::ts => M p t ≡ 3 [MOD 10] ∧ ¬ 3 ∣ M p t ∧ ordinaryRecordWords (state p t) ts

private theorem ordinary_word_product (p : ℕ) (ts : List ℕ) (words : ordinaryRecordWords p ts) :
    M p ts.sum ≡ 3^ts.length [MOD 10] ∧ ¬ 3 ∣ M p ts.sum := by
  induction ts generalizing p with
  | nil => change 1 ≡ 1 [MOD 10] ∧ ¬ 3 ∣ 1; decide
  | cons t ts ih =>
    obtain ⟨digit,three,rest⟩ := words
    obtain ⟨tail,free⟩ := ih (state p t) rest
    rw [List.sum_cons,cofactor_product_append,List.length_cons,pow_succ']
    exact ⟨digit.mul tail,fun h => (Nat.prime_three.dvd_mul.mp h).elim three free⟩

/-- A nonempty ordinary transfer with its true unit first edge supplies both
    premises of the digit budget: its starting digit and its exact transport. -/
theorem actual_ordinary_transfer {p : ℕ} (hp : p.Prime) (large : 11 ≤ p) (ts : List ℕ)
    (nonempty : 0 < ts.sum) (unit : cofactor p 0 = 1) (high : 3 < state p 2)
    (records : ordinaryRecordWords (state p 1) ts) :
    (lastDigit p = 3 ∨ lastDigit p = 9) ∧
      (3^ts.length*lastDigit (state p (1+ts.sum)))%10 = lastDigit p := by
  obtain ⟨digits,free⟩ := ordinary_word_product _ _ records
  have full : M p (1+ts.sum) = M (state p 1) ts.sum := by
    rw [cofactor_product_append]
    simp [M,unit]
  have no17 : ¬ (lastDigit p=1 ∨ lastDigit p=7) := by
    intro bad
    have hit := (pure_ascent_forces_three hp large bad unit high).trans
      (cofactor_dvd_word p (i := 1) (t := 1+ts.sum) (by omega))
    exact free (full ▸ hit)
  have cop (a : ℕ) (lo : 1 < a) (hi : a < p) : p%a ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_iff_mod_eq_zero.mpr h) with eq | eq <;> omega
  have odd := cop 2 (by decide) (by omega)
  have five := cop 5 (by decide) (by omega)
  refine ⟨by unfold lastDigit at *; omega,?_⟩
  have transport := product_last_digit hp (1+ts.sum)
  rw [full] at transport
  have congr := (digits.mul_right (state p (1+ts.sum))).symm
  change (3^ts.length * state p (1+ts.sum))%10 =
    (M (state p 1) ts.sum * state p (1+ts.sum))%10 at congr
  simpa [lastDigit,Nat.mul_mod] using congr.trans transport

def transferWeight (d : ℕ) := if d=9 then 2 else if d=3 ∨ d=7 then 1 else 0

private theorem weight_table : ∀ x y : Fin 10, ∀ k : Fin 4,
    (x.val=3 ∨ x.val=9) → 0<k.val → (3^k.val*y.val)%10=x.val →
    2 + transferWeight y.val ≤ k.val + transferWeight x.val := by decide

private theorem weight_bound (d : ℕ) : transferWeight d ≤ 2 := by
  unfold transferWeight
  split_ifs <;> omega

/-- The number of records and exceptional records over arbitrary many
    nonempty transfers. End digit of one transfer is the next start digit. -/
theorem record_transfer_count (digits blocks errors : ℕ → ℕ) (n : ℕ)
    (units : ∀ i ≤ n, digits i < 10)
    (nonempty : ∀ i < n, 0 < blocks i)
    (ordinary : ∀ i < n, errors i = 0 → (digits i = 3 ∨ digits i = 9) ∧
      (3^(blocks i)*digits (i+1))%10 = digits i) :
    2*n + transferWeight (digits n) ≤
      (∑ i ∈ range n, blocks i) + 3*(∑ i ∈ range n, errors i) + transferWeight (digits 0) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have old := ih (fun i hi => units i (by omega)) (fun i hi => nonempty i (by omega))
      (fun i hi => ordinary i (by omega))
    have bpos := nonempty k (by omega)
    have wmax := weight_bound (digits (k+1))
    have cost : 2+transferWeight (digits (k+1)) ≤ blocks k + 3*errors k + transferWeight (digits k) := by
      by_cases noError : errors k = 0
      · obtain ⟨d,rel⟩ := ordinary k (by omega) noError
        by_cases small : blocks k < 4
        · have tab := weight_table ⟨digits k,units k (by omega)⟩ ⟨digits (k+1),units (k+1) le_rfl⟩
            ⟨blocks k,small⟩ d bpos rel
          simpa only [noError,Nat.mul_zero,Nat.add_zero] using tab
        · omega
      · omega
    rw [sum_range_succ,sum_range_succ]
    omega

end PrimeDynamics
