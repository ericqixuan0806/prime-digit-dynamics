import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic

namespace PrimeDynamics

open Finset
open scoped BigOperators

/-- Positive excesses are summable when the normalized heights have a positive
    lower bound and their exact products against those heights stay bounded. -/
theorem summable_record_excess {e V L : ℕ → ℝ} {a U : ℝ}
    (he : ∀ i, 0 ≤ e i) (ha : 0 < a) (floor : ∀ n, a ≤ V n)
    (budget : ∀ n, L n ≤ U)
    (balance : ∀ n, (∏ i ∈ range n, (1 + e i)) * V n = L n) : Summable e := by
  have lower (n : ℕ) : 1 + ∑ i ∈ range n, e i ≤ ∏ i ∈ range n, (1 + e i) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ,prod_range_succ]
      have nonneg : 0 ≤ ∑ i ∈ range n, e i := sum_nonneg (fun i _ => he i)
      have extra := mul_nonneg nonneg (he n)
      have scaled := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+e n by linarith [he n])
      nlinarith only [extra,scaled]
  apply summable_of_sum_range_le he (c := U/a)
  intro n
  have hprod : 0 ≤ ∏ i ∈ range n, (1 + e i) := prod_nonneg (fun i _ => by linarith [he i])
  have up := mul_le_mul_of_nonneg_left (floor n) hprod
  rw [balance] at up
  apply (le_div_iff₀ ha).mpr
  exact (mul_le_mul_of_nonneg_right (le_trans (by linarith) (lower n)) ha.le).trans
    (up.trans (budget n))

/-- A positive lower bound on the normalized heights is needed only at
    cofinal excursion endpoints, even when each excursion contains many records. -/
theorem summable_record_excess_at_cuts {e V : ℕ → ℝ} {a U : ℝ} (cut : ℕ → ℕ)
    (he : ∀ i, 0 ≤ e i) (ha : 0 < a) (floor : ∀ j, a ≤ V j)
    (cofinal : ∀ n, ∃ j, n ≤ cut j)
    (budget : ∀ j, (∏ i ∈ range (cut j), (1+e i)) * V j ≤ U) : Summable e := by
  let P := fun n : ℕ => ∏ i ∈ range n, (1+e i)
  have pos (n : ℕ) : 0 ≤ P n := prod_nonneg (fun i _ => by linarith [he i])
  have mono : Monotone P := monotone_nat_of_le_succ fun n => by
    change P n ≤ ∏ i ∈ range (n+1), (1+e i)
    rw [prod_range_succ]
    exact le_mul_of_one_le_right (pos n) (by linarith [he n])
  apply summable_record_excess (V := fun _ => a) (L := fun n => P n*a) (U := U)
    he ha (fun _ => le_rfl) _ (fun _ => rfl)
  intro n
  obtain ⟨j,hj⟩ := cofinal n
  exact (mul_le_mul_of_nonneg_right (mono hj) ha.le).trans
    ((mul_le_mul_of_nonneg_left (floor j) (pos (cut j))).trans (budget j))

/-- From counts in dyadic shells to a bound for the reciprocal tail.
    The majorant is an explicit summable input. No sieve theorem is assumed as an axiom. -/
theorem reciprocal_tail_of_shell_counts (S : ℕ → Prop) [DecidablePred S] (Y : ℕ)
    (hy : 0 < Y) (c : ℕ → ℝ) (hc : Summable c)
    (hc0 : ∀ j, 0 ≤ c j)
    (counts : ∀ j, (((Ico (2^j*Y) (2^(j+1)*Y)).filter S).card : ℝ) ≤
      c j * ((2^j*Y : ℕ) : ℝ)) :
    let f := fun q : ℕ => if Y ≤ q ∧ S q then 1/(q:ℝ) else 0
    Summable f ∧ ∑' q, f q ≤ ∑' j, c j := by
  classical
  let f := fun q : ℕ => if Y ≤ q ∧ S q then 1/(q:ℝ) else 0
  change Summable f ∧ ∑' q, f q ≤ ∑' j, c j
  let cut := fun j : ℕ => 2^j*Y
  have pos (j : ℕ) : 0 < cut j := Nat.mul_pos (by positivity) hy
  have size (j : ℕ) : Y ≤ cut j := by
    exact Nat.le_mul_of_pos_left Y (by positivity)
  have fn (q : ℕ) : 0 ≤ f q := by dsimp [f]; split <;> positivity
  have shell (j : ℕ) : ∑ q ∈ Ico (cut j) (cut (j+1)), f q ≤ c j := by
    let s := (Ico (cut j) (cut (j+1))).filter S
    have bound : ∑ q ∈ Ico (cut j) (cut (j+1)), f q ≤ ∑ _q ∈ s, 1/(cut j:ℝ) := by
      unfold s
      rw [sum_filter]
      apply sum_le_sum
      intro q hq
      have above := (mem_Ico.mp hq).1
      by_cases keep : S q
      · simp only [f, (size j).trans above,keep,and_self,if_true]
        exact one_div_le_one_div_of_le (by exact_mod_cast pos j) (by exact_mod_cast above)
      · simp [f,keep]
    have cn := counts j
    change (s.card:ℝ) ≤ c j * (cut j : ℝ) at cn
    calc
      _ ≤ _ := bound
      _ = (s.card:ℝ)/(cut j:ℝ) := by simp [nsmul_eq_mul, div_eq_mul_inv]
      _ ≤ c j := (div_le_iff₀ (by exact_mod_cast pos j)).mpr cn
  have prefixes (n : ℕ) : ∑ q ∈ range (cut n), f q ≤ ∑ j ∈ range n, c j := by
    induction n with
    | zero =>
      have nil : ∑ q ∈ range (cut 0), f q = 0 := by
        apply sum_eq_zero
        intro q hq
        have h : q < Y := by simpa [cut] using mem_range.mp hq
        simp [f, Nat.not_le_of_gt h]
      simp [nil]
    | succ n ih =>
      have mono : cut n ≤ cut (n+1) := by
        dsimp [cut]; rw [pow_succ];
        nlinarith only [Nat.zero_le (2^n*Y)]
      rw [← sum_range_add_sum_Ico f mono, sum_range_succ]
      exact add_le_add ih (shell n)
  have allBounds (n : ℕ) : ∑ q ∈ range n, f q ≤ ∑' j, c j := by
    have large : n ≤ cut n := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans
      (Nat.le_mul_of_pos_right (2^n) hy)
    exact (sum_le_sum_of_subset_of_nonneg (range_mono large) (fun i _ _ => fn i)).trans
      ((prefixes n).trans (hc.sum_le_tsum _ (fun i _ => hc0 i)))
  exact ⟨summable_of_sum_range_le fn allBounds, Real.tsum_le_of_sum_range_le fn allBounds⟩

end PrimeDynamics
