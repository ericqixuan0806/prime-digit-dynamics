import PrimeDynamics.RecordProducts
import PrimeDynamics.CycleRunDivisors
import Mathlib.Data.Nat.ModEq

open Nat

namespace PrimeDynamics

/-- A large prefix prime and the distinct last division cannot both fit
    into a small-excess record. The last cofactor itself is at least eleven. -/
theorem record_prime_below_seed {p n e q : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (above : p ≤ state p n) (down : state p (n+1) < p)
    (excess : M p (n+1) = 10^(n+1)+e) (small : e ≤ 11*(p-state p (n+1)))
    (hq : q.Prime) (hit : q ∣ M p (n+1)) : q < p := by
  let y := state p (n+1)
  have equation := affine_identity hp (n+1)
  have split : p-y+y = p := Nat.sub_add_cancel down.le
  have scaled := congrArg (fun w => M p (n+1)*w) split
  change M p (n+1)*(p-y+y) = M p (n+1)*p at scaled
  rw [Nat.mul_add] at scaled
  change M p (n+1)*y = 10^(n+1)*p + C p (n+1) at equation
  have atP := congrArg (fun w => w*p) excess
  change M p (n+1)*p = (10^(n+1)+e)*p at atP
  rw [Nat.add_mul] at atP
  have positive := intercept_pos hp large n
  have paid := Nat.mul_le_mul_right p small
  have upper : M p (n+1) < 11*p := by
    apply Nat.lt_of_mul_lt_mul_right (a := p-y)
    nlinarith only [scaled,atP,equation,positive,paid]
  have edge := step_factor hp n
  change cofactor p n*y = 10*state p n+lastDigit (state p n) at edge
  have last : 11 ≤ cofactor p n := by
    by_contra! h
    have atY := Nat.mul_le_mul_right y (show cofactor p n ≤ 10 by omega)
    change y < p at down
    omega
  change q ∣ M p n * cofactor p n at hit
  rcases hq.dvd_mul.mp hit with early | final
  · have pos : 0 < M p n := by
      by_contra! zero
      have hz : M p n = 0 := by omega
      simp [M,hz] at excess
      have : 0 < (10:ℕ)^(n+1) := by positivity
      omega
    have atLeast := Nat.mul_le_mul (Nat.le_of_dvd pos early) last
    change M p n * cofactor p n < 11*p at upper
    omega
  · have d := dvd_mul_of_dvd_left final (state p (n+1))
    rw [step_factor hp] at d
    have upperQ := le_largestPrimeFactor (extend_gt_one (iterate_prime hp n).pos) hq d
    have bound : q ≤ state p (n+1) := by
      simpa [state,Function.iterate_succ_apply',T] using upperQ
    exact bound.trans_lt down

/-- Multiplying the pure decimal recurrence by nine removes the denominator. -/
theorem pureRun_scaled_shift (x i s : ℕ) :
    9*pureRun x (i+s)+lastDigit x = 10^s*(9*pureRun x i+lastDigit x) := by
  induction s with
  | zero => simp
  | succ s ih =>
    change 9*(10*pureRun x (i+s)+lastDigit (pureRun x (i+s)))+lastDigit x = _
    rw [pureRun_digit,pow_succ]
    nlinarith only [ih]

/-- No positive return exponent through a pure run can occur at a small
    divisor of its closing extension when all preceding states are larger primes. -/
theorem no_short_return_in_run {x h q s : ℕ} (hq : q.Prime) (nine : ¬ q ∣ 9)
    (states : ∀ i < h, (pureRun x i).Prime ∧ q < pureRun x i)
    (hit : q ∣ pureRun x h) (positive : 0 < s) (short : s ≤ h) :
    ¬ (10^s ≡ 1 [MOD q]) := by
  intro ret
  let i := h-s
  have idx : i+s = h := Nat.sub_add_cancel short
  have back := pureRun_scaled_shift x i s
  rw [idx] at back
  have same : 9*pureRun x h+lastDigit x ≡ 9*pureRun x i+lastDigit x [MOD q] := by
    rw [back]
    simpa only [one_mul] using ret.mul_right (9*pureRun x i+lastDigit x)
  have undo := same.add_right_cancel' (lastDigit x)
  have divides : q ∣ 9*pureRun x i := Nat.modEq_zero_iff_dvd.mp
    (undo.symm.trans (dvd_mul_of_dvd_right hit 9).modEq_zero_nat)
  have atI := (hq.dvd_mul.mp divides).resolve_left nine
  obtain ⟨primeI,ltI⟩ := states i (by dsimp [i]; omega)
  rcases (Nat.dvd_prime primeI).mp atI with one | eq
  · exact hq.ne_one one
  · omega

/-- A prime shared by two products of the same excess yields a return
    exponent for ten, without an assumption on the other prime factors. -/
theorem shared_excess_return {q e t s : ℕ} (cop : q.Coprime 10)
    (first : q ∣ 10^t+e) (second : q ∣ 10^(t+s)+e) : 10^s ≡ 1 [MOD q] := by
  have both := second.modEq_zero_nat.trans first.modEq_zero_nat.symm
  have powers := both.add_right_cancel' e
  rw [pow_add] at powers
  apply Nat.ModEq.cancel_left_of_coprime (cop.pow_right t).gcd_eq_one
  simpa only [mul_one] using powers

/-- On the same prime support, the distinct length gap must exceed the
    entire run ending at the marked factor. -/
theorem shared_excess_run_spacing {x h q e t s : ℕ} (hq : q.Prime) (cop : q.Coprime 10)
    (nine : ¬ q ∣ 9) (states : ∀ i < h, (pureRun x i).Prime ∧ q < pureRun x i)
    (hit : q ∣ pureRun x h) (first : q ∣ 10^t+e) (second : q ∣ 10^(t+s)+e)
    (positive : 0 < s) : h < s := by
  by_contra! short
  exact no_short_return_in_run hq nine states hit positive short (shared_excess_return cop first second)

theorem cofactor_dvd_word (p : ℕ) {i t : ℕ} (lt : i < t) : cofactor p i ∣ M p t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases eq : i=t
    · subst i; exact dvd_mul_left _ _
    · exact dvd_mul_of_dvd_left (ih (by omega)) _

/-- A marked edge in a first descent. All earlier states of its pure
    run are actual primes above the seed, so the spacing test applies. -/
theorem actual_record_no_short_return {p n i k e q s : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (above : ∀ j < n+1, p ≤ state p j) (down : state p (n+1) < p)
    (excess : M p (n+1) = 10^(n+1)+e) (small : e ≤ 11*(p-state p (n+1)))
    (inside : i+k < n+1) (units : ∀ j < k, cofactor (state p i) j = 1)
    (hq : q.Prime) (nine : ¬ q ∣ 9) (hit : q ∣ cofactor p (i+k))
    (positive : 0 < s) (short : s ≤ k+1) : ¬ (10^s ≡ 1 [MOD q]) := by
  have hpi : (state p i).Prime := iterate_prime hp i
  have below := record_prime_below_seed hp large (above n (by omega)) down excess small hq
    (hit.trans (cofactor_dvd_word p inside))
  rw [cofactor_shift] at hit
  have last := dvd_mul_of_dvd_left hit (state (state p i) (k+1))
  rw [step_factor hpi, (actual_pure_prefix hpi k units).1] at last
  apply no_short_return_in_run hq nine (x := state p i) (h := k+1) _ last positive short
  intro j hj
  rw [← (actual_pure_prefix hpi j (fun l hl => units l (by omega))).1, ← state_add]
  exact ⟨iterate_prime hp _,below.trans_le (above (i+j) (by omega))⟩

private theorem ten_three_coprime_ninety (n : ℕ) : (10^(n+1)+3).Coprime 90 := by
  have power : 10^(n+1) ≡ 10 [MOD 90] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ]
      exact (ih.mul_right 10).trans (by decide)
  exact (power.add_right 3).gcd_eq.trans (by decide : Nat.gcd (10+3) 90 = 1)

/-- If the sole division in an excess-three first descent is its last step,
    the whole cofactor is coprime to every earlier term of the numerical sequence. -/
theorem single_excess_three_coprime {p n r : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (above : ∀ j < n+1, p ≤ state p j) (down : state p (n+1) < p)
    (excess : M p (n+1) = 10^(n+1)+3) (units : ∀ j < n, cofactor p j = 1)
    (earlier : r < n+1) : (10^(n+1)+3).Coprime (10^r+3) := by
  apply Nat.coprime_of_dvd
  intro q prime high low
  have cop90 := (ten_three_coprime_ninety n).of_dvd_left high
  have cop10 : q.Coprime 10 := cop90.of_dvd_right (by decide)
  have noNine := prime.coprime_iff_not_dvd.mp (cop90.of_dvd_right (by decide : 9 ∣ 90))
  have tail : q ∣ cofactor p n := by
    rw [← excess,M,(actual_pure_prefix hp n units).2,one_mul] at high
    exact high
  let d := n+1-r
  have idx : r+d = n+1 := Nat.add_sub_of_le earlier.le
  have ret : 10^d ≡ 1 [MOD q] := shared_excess_return cop10 low (idx ▸ high)
  have bound : 3 ≤ 11*(p-state p (n+1)) := by omega
  have reject := actual_record_no_short_return (i := 0) (k := n) (s := d) hp large
    above down excess bound (by omega) (by simpa [state] using units) prime noNine
    (by simpa using tail) (by dsimp [d]; omega) (by dsimp [d]; omega)
  exact reject ret

/-- Two consecutive first descents with excess three can use disjoint supports
    even when every prime in the displayed segment exceeds the finite base. -/
theorem adjacent_three_excess_example :
    Nat.Prime 292759 ∧ T 292759 = 2927599 ∧ T 2927599 = 284233 ∧ T 284233 = 218641 ∧
    (103:ℕ).Coprime 13 ∧ 103 = 10^2+3 ∧ 13 = 10^1+3 := by
  exact ⟨Certificate.primeOK_sound (by rfl),
    Certificate.edgeOK_sound (fs := [2927599]) (by rfl),
    Certificate.edgeOK_sound (fs := [103,284233]) (by rfl),
    Certificate.edgeOK_sound (fs := [13,218641]) (by rfl),by decide,by decide,by decide⟩

end PrimeDynamics
