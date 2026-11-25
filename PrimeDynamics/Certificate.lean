import PrimeDynamics.TrialData

namespace PrimeDynamics.Certificate

/-- A balanced interval check keeps the kernel reduction stack shallow. -/
def block (f : ℕ → Bool) (s : ℕ) : ℕ → Bool
  | 0 => f s
  | k+1 => block f s k && block f (s + 2^k) k

theorem block_join {f : ℕ → Bool} {s k : ℕ} (left : block f s k = true)
    (right : block f (s + 2^k) k = true) : block f s (k+1) = true := by
  simp [block,left,right]

theorem block_sound {f : ℕ → Bool} {s k m : ℕ} (h : block f s k = true)
    (lo : s ≤ m) (hi : m < s + 2^k) : f m = true := by
  induction k generalizing s with
  | zero =>
    simp only [pow_zero] at hi
    have : m = s := by omega
    simpa [this] using h
  | succ k ih =>
    have hh : block f s k = true ∧ block f (s+2^k) k = true := by simpa [block] using h
    rw [pow_succ] at hi
    by_cases hm : m < s + 2^k
    · exact ih hh.1 lo hm
    · exact ih hh.2 (by omega) (by omega)

/-- Skip a whole interval as soon as its left endpoint exceeds the square root. -/
def trial (p s : ℕ) : ℕ → Bool
  | 0 => decide (p < s*s) || decide (p%s ≠ 0)
  | k+1 => decide (p < s*s) || (trial p s k && trial p (s + 2^k) k)

theorem trial_sound {p s k m : ℕ} (h : trial p s k = true)
    (lo : s ≤ m) (hi : m < s + 2^k) (hm : m ≤ Nat.sqrt p) : ¬m ∣ p := by
  have hs : ¬p < s*s := fun hl => (not_lt_of_ge (lo.trans hm)) (Nat.sqrt_lt.mpr hl)
  induction k generalizing s with
  | zero =>
    simp only [pow_zero] at hi
    have he : m = s := by omega
    subst m
    simpa [trial, hs, Nat.dvd_iff_mod_eq_zero] using h
  | succ k ih =>
    have hh : trial p s k = true ∧ trial p (s+2^k) k = true := by simpa [trial, hs] using h
    rw [pow_succ] at hi
    by_cases hh' : m < s + 2^k
    · exact ih hh.1 lo hh' hs
    · have lower : s+2^k ≤ m := by omega
      exact ih hh.2 lower (by omega) (fun hl => (not_lt_of_ge (lower.trans hm)) (Nat.sqrt_lt.mpr hl))

def primeOK (p : ℕ) : Bool :=
  if p ≤ 16 then decide (2 ≤ p) && trial p 2 2
  else if p ≤ 256 then decide (Nat.gcd p TrialProducts.f4 = 1)
  else if p ≤ 65536 then decide (Nat.gcd p TrialProducts.f8 = 1)
  else if p ≤ 16777216 then decide (Nat.gcd p TrialProducts.f12 = 1)
  else decide (p ≤ 4294967296) && decide (Nat.gcd p TrialProducts.f16 = 1)

theorem primeOK_sound {p : ℕ} (h : primeOK p = true) : p.Prime := by
  unfold primeOK at h
  split at h
  · have hh : 2 ≤ p ∧ trial p 2 2 = true := by simpa using h
    refine Nat.prime_def_le_sqrt.mpr ⟨hh.1, fun m lo hi => ?_⟩
    have bound : Nat.sqrt p < 2+2^2 := Nat.sqrt_lt.mpr (by omega)
    exact trial_sound hh.2 lo (hi.trans_lt bound) hi
  split at h
  · exact TrialProducts.prime_of_coprime (by omega) (by norm_num; omega)
      TrialProducts.f4_ok (of_decide_eq_true h)
  split at h
  · exact TrialProducts.prime_of_coprime (by omega) (by norm_num; omega)
      TrialProducts.f8_ok (of_decide_eq_true h)
  split at h
  · exact TrialProducts.prime_of_coprime (by omega) (by norm_num; omega)
      TrialProducts.f12_ok (of_decide_eq_true h)
  · have hh : p ≤ 4294967296 ∧ Nat.gcd p TrialProducts.f16 = 1 := by simpa using h
    exact TrialProducts.prime_of_coprime (by omega) (by norm_num; omega) TrialProducts.f16_ok hh.2

def edgeOK (p q : ℕ) (fs : List ℕ) : Bool :=
  decide (0 < p) && (decide (fs.prod = digitExtend p) &&
    (fs.contains q && fs.all (fun x => primeOK x && decide (x ≤ q))))

theorem edgeOK_sound {p q : ℕ} {fs : List ℕ} (h : edgeOK p q fs = true) : T p = q := by
  have h' : 0 < p ∧ fs.prod = digitExtend p ∧ q ∈ fs ∧
      ∀ x ∈ fs, primeOK x = true ∧ x ≤ q := by
    simpa [edgeOK, List.contains_iff_mem] using h
  obtain ⟨hp,hprod,hq,hall⟩ := h'
  have perm := Nat.primeFactorsList_unique hprod (fun x hx => primeOK_sound (hall x hx).1)
  have hs : T p ∈ fs := perm.mem_iff.mpr (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp
    (largestPrimeFactor_mem (extend_gt_one hp)))
  have hq' := Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr (perm.mem_iff.mp hq)
  exact le_antisymm (hall _ hs).2
    (le_largestPrimeFactor (extend_gt_one hp) (Nat.prime_of_mem_primeFactors hq')
      (Nat.dvd_of_mem_primeFactors hq'))

structure Row where
  p : ℕ
  next : ℕ
  factors : List ℕ
  deriving Inhabited

def rowOK (row : ℕ → Row) (i : ℕ) : Bool :=
  let r := row i
  cycle.contains r.p || (decide (r.next < i) && edgeOK r.p (row r.next).p r.factors)

theorem reaches_of_rows {row : ℕ → Row} {B : ℕ} (h : ∀ i < B, rowOK row i = true) :
    ∀ i < B, Reaches (row i).p := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hok : (row i).p ∈ cycle ∨ ((row i).next < i ∧
        edgeOK (row i).p (row (row i).next).p (row i).factors = true) := by
      simpa [rowOK, List.contains_iff_mem] using h i hi
    rcases hok with hc | ⟨hlt, he⟩
    · exact ⟨0, hc⟩
    · exact reaches_predecessor (edgeOK_sound he) (ih _ hlt (hlt.trans hi))

/-- A witness points to a row or gives a proper divisor of the putative prime. -/
def coverOK (row : ℕ → Row) (B p w : ℕ) : Bool :=
  decide (p < 2) || (decide (w < B ∧ (row w).p = p) || decide (1 < w ∧ w < p ∧ p % w = 0))

theorem covered_prime {row : ℕ → Row} {B p w : ℕ} (hp : p.Prime)
    (hrow : ∀ i < B, Reaches (row i).p) (h : coverOK row B p w = true) : Reaches p := by
  have h' : p < 2 ∨ (w < B ∧ (row w).p = p) ∨ (1 < w ∧ w < p ∧ p % w = 0) := by
    simpa [coverOK] using h
  rcases h' with small | ⟨hi, he⟩ | ⟨h1, h2, h3⟩
  · exact (not_lt_of_ge hp.two_le small).elim
  · exact he ▸ hrow w hi
  · have hv := (Nat.dvd_prime hp).mp (Nat.dvd_iff_mod_eq_zero.mpr h3)
    omega

end PrimeDynamics.Certificate
