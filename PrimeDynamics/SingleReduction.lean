import PrimeDynamics.OrbitContraction
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace PrimeDynamics

def repunit : ℕ → ℕ
  | 0 => 0
  | i+1 => 10 * repunit i + 1

def pureRun (p : ℕ) : ℕ → ℕ
  | 0 => p
  | i+1 => digitExtend (pureRun p i)

theorem repunit_identity (i : ℕ) : 9 * repunit i + 1 = 10^i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [repunit,pow_succ,← ih]; ring

theorem pureRun_digit (p i : ℕ) : lastDigit (pureRun p i) = lastDigit p := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (10 * pureRun p i + lastDigit (pureRun p i)) % 10 = lastDigit p
    rw [ih]
    unfold lastDigit
    omega

theorem pureRun_affine (p i : ℕ) : pureRun p i = 10^i*p + lastDigit p * repunit i := by
  induction i with
  | zero => simp [pureRun,repunit]
  | succ i ih =>
    rw [pureRun,digitExtend,pureRun_digit,ih,repunit,pow_succ]
    ring

private theorem repunit_dvd_iff {p i : ℕ} (hp : p.Prime) (big : 11 ≤ p) :
    p ∣ pureRun p i ↔ p ∣ repunit i := by
  have notDigit : ¬ p ∣ lastDigit p := by
    intro hd
    have pos : 0 < lastDigit p := by
      by_contra! hz
      have dvd : 10 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr (show p%10=0 by unfold lastDigit at hz; omega)
      rcases (Nat.dvd_prime hp).mp dvd with hh | hh <;> omega
    have le := Nat.le_of_dvd pos hd
    unfold lastDigit at le
    omega
  rw [pureRun_affine, Nat.dvd_add_right (dvd_mul_left p (10^i))]
  exact ⟨fun h => (hp.dvd_mul.mp h).resolve_left notDigit, fun h => dvd_mul_of_dvd_right h _⟩

/-- For a closed orbit with a single non-unit cofactor, n is the first positive
    repunit divisible by its minimum. The last (possibly composite) extended
    integer only needs the closing prime as a divisor. -/
theorem single_reduction_order {p n : ℕ} (hp : p.Prime) (big : 11 ≤ p)
    (primePrefix : ∀ i < n, (pureRun p i).Prime) (close : p ∣ pureRun p n) :
    p ∣ repunit n ∧ ∀ i, 0 < i → i < n → ¬ p ∣ repunit i := by
  refine ⟨(repunit_dvd_iff hp big).mp close,?_⟩
  intro i positive before divides
  have hv := (repunit_dvd_iff hp big).mpr divides
  rcases (Nat.dvd_prime (primePrefix i before)).mp hv with eq | eq
  · omega
  · have ten : 1 < (10:ℕ)^i := one_lt_pow₀ (by decide) (by omega)
    have gt := Nat.mul_lt_mul_of_pos_right ten hp.pos
    rw [pureRun_affine] at eq
    omega

theorem repunit_add (a b : ℕ) : repunit (a+b) = 10^b * repunit a + repunit b := by
  induction b with
  | zero => simp [repunit]
  | succ b ih =>
    change 10 * repunit (a+b) + 1 = 10^(b+1)*repunit a+(10*repunit b+1)
    rw [ih,pow_succ]
    ring

/-- All divisible repunits, with no bound on the index. -/
theorem single_reduction_multiples {p n : ℕ} (hp : p.Prime) (big : 11 ≤ p) (hn : 0 < n)
    (primePrefix : ∀ i < n, (pureRun p i).Prime) (close : p ∣ pureRun p n) (i : ℕ) :
    p ∣ repunit i ↔ n ∣ i := by
  obtain ⟨first, before⟩ := single_reduction_order hp big primePrefix close
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases small : i < n
    · by_cases zero : i = 0
      · simp [zero,repunit]
      · have ipos : 0 < i := Nat.pos_of_ne_zero zero
        exact ⟨fun hit => (before i ipos small hit).elim,
          fun hit => (not_lt_of_ge (Nat.le_of_dvd ipos hit) small).elim⟩
    · let j := i-n
      have split : n+j = i := by dsimp [j]; omega
      have rest := ih j (by dsimp [j]; omega)
      calc
        p ∣ repunit i ↔ p ∣ repunit (n+j) := by rw [split]
        _ ↔ p ∣ repunit j := by
          rw [repunit_add, Nat.dvd_add_right (dvd_mul_of_dvd_right first (10^j))]
        _ ↔ n ∣ j := rest
        _ ↔ n ∣ n+j := (Nat.dvd_add_right (dvd_refl n)).symm
        _ ↔ n ∣ i := by rw [split]

def pureBlockRatio (p h : ℕ) : ℚ := (pureRun p h : ℚ) / ((10:ℚ)^h * (p:ℚ))

/-- Arbitrary many blocks, each made of pure extensions and one division.
    On a cycle the first and final heights cancel. -/
theorem pure_blocks_product (x h m : ℕ → ℕ) (b : ℕ)
    (pos : ∀ i ≤ b, 0 < x i) (word : ∀ i < b, m i * x (i+1) = pureRun (x i) (h i)) :
    (∏ i ∈ Finset.range b, (m i : ℚ)) * (x b : ℚ) =
      (10:ℚ)^(∑ i ∈ Finset.range b, h i) * (x 0 : ℚ) *
      (∏ i ∈ Finset.range b, pureBlockRatio (x i) (h i)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have old := ih (fun i hi => pos i (by omega)) (fun i hi => word i (by omega))
    have piece : (m b:ℚ)*(x (b+1):ℚ) = (10:ℚ)^(h b)*(x b:ℚ)*pureBlockRatio (x b) (h b) := by
      have nonzero : (10:ℚ)^(h b)*(x b:ℚ) ≠ 0 :=
        mul_ne_zero (by positivity) (by exact_mod_cast (pos b (by omega)).ne')
      rw [pureBlockRatio, mul_div_cancel₀ _ nonzero]
      exact_mod_cast word b (by omega)
    rw [Finset.prod_range_succ,Finset.prod_range_succ,Finset.sum_range_succ,pow_add]
    calc
      _ = (∏ i ∈ Finset.range b, (m i:ℚ)) * ((m b:ℚ)*(x (b+1):ℚ)) := by ring
      _ = ((∏ i ∈ Finset.range b, (m i:ℚ)) * (x b:ℚ)) *
          ((10:ℚ)^(h b)*pureBlockRatio (x b) (h b)) := by rw [piece]; ring
      _ = _ := by rw [old]; ring

theorem repunit_dvd_of_dvd {h n : ℕ} (divides : h ∣ n) : repunit h ∣ repunit n := by
  obtain ⟨k,rfl⟩ := divides
  induction k with
  | zero => simp [repunit]
  | succ k ih =>
    rw [Nat.mul_succ,repunit_add]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_refl _)

/-- For a single reduction, each proper positive divisor of the period
    forces a divisor of the exact product excess, including the initial digit. -/
theorem single_reduction_gap_divisor {p n e h : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (primePrefix : ∀ i < n, (pureRun p i).Prime)
    (edge : (10^n+e)*p = pureRun p n) (hh : 0 < h) (before : h < n) (divides : h ∣ n) :
    lastDigit p * repunit h ∣ e := by
  have close : p ∣ pureRun p n := by rw [← edge]; exact dvd_mul_left p _
  obtain ⟨atEnd,earlier⟩ := single_reduction_order hp large primePrefix close
  obtain ⟨u,hu⟩ := atEnd
  have cop := (hp.coprime_iff_not_dvd.mpr (earlier h hh before)).symm
  have allDiv := repunit_dvd_of_dvd divides
  rw [hu] at allDiv
  have part : repunit h ∣ u := cop.dvd_of_dvd_mul_left allDiv
  have prodEq : e*p = lastDigit p * (p*u) := by
    rw [pureRun_affine,Nat.add_mul,hu] at edge
    omega
  have eg : e = lastDigit p*u := Nat.eq_of_mul_eq_mul_right hp.pos
    (show e*p = (lastDigit p*u)*p by rw [prodEq]; ring)
  exact eg ▸ Nat.mul_dvd_mul_left (lastDigit p) part

end PrimeDynamics
