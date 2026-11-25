import PrimeDynamics.ReciprocalBudget
import PrimeDynamics.Certificate
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp

namespace PrimeDynamics

/-- All states through time r are at least the seed. -/
def Survives (p r : ℕ) : Prop := ∀ i ≤ r, p ≤ state p i

theorem product_height_bound {p : ℕ} (hp : p.Prime) (i : ℕ) :
    M p i * state p i ≤ 11^i * p := by
  induction i with
  | zero => simp [M,state]
  | succ i ih =>
    have he : digitExtend (state p i) ≤ 11 * state p i := by
      have := Nat.mod_le (state p i) 10
      unfold digitExtend lastDigit
      omega
    calc
      M p (i+1) * state p (i+1) = M p i * digitExtend (state p i) := by
        rw [M, Nat.mul_assoc, step_factor hp]
      _ ≤ M p i * (11 * state p i) := Nat.mul_le_mul_left _ he
      _ = 11 * (M p i * state p i) := by ring
      _ ≤ 11 * (11^i * p) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ring

theorem cofactor_cap {p i : ℕ} (hp : p.Prime) (above : p ≤ state p i) :
    M p i ≤ 11^i := by
  have h := (Nat.mul_le_mul_left (M p i) above).trans (product_height_bound hp i)
  exact Nat.le_of_mul_le_mul_right h hp.pos

theorem intercept_cap {p : ℕ} (hp : p.Prime) (n : ℕ)
    (above : ∀ i < n, p ≤ state p i) : C p n + 9*10^n ≤ 9*11^n := by
  induction n with
  | zero => simp [C]
  | succ n ih =>
    have old := ih (fun i hi => above i (by omega))
    have digit : lastDigit (state p n) ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
    have term := Nat.mul_le_mul digit (cofactor_cap hp (above n (by omega)))
    rw [C, pow_succ, pow_succ]
    omega

/-- A first descent within r steps has a uniform relative gap above a seed threshold. -/
theorem descent_gap {p j r : ℕ} (hp : p.Prime) (hj : j ≤ r)
    (prior : ∀ h < j, p ≤ state p h) (down : state p j < p)
    (large : 18*11^r ≤ p) :
    2*(10^r+1)*state p j + p ≤ 2*(10^r+1)*p := by
  have hm : 10^j < M p j := by
    by_contra! small
    exact (Nat.not_lt.mpr (no_descent_before_crossing hp small)) down
  have hc := intercept_cap hp j prior
  have h11 : (11:ℕ)^j ≤ 11^r := Nat.pow_le_pow_right (by decide) hj
  have err : 2*C p j ≤ p := by omega
  have hmul := Nat.mul_le_mul_right (state p j) (Nat.succ_le_of_lt hm)
  rw [affine_identity hp, Nat.succ_mul] at hmul
  have h10 : (10:ℕ)^j ≤ 10^r := Nat.pow_le_pow_right (by decide) hj
  have mono := Nat.mul_le_mul_right (p-state p j) h10
  rw [Nat.mul_sub, Nat.mul_sub] at mono
  have jbound := Nat.mul_le_mul_left (10^j) down.le
  have rbound := Nat.mul_le_mul_left (10^r) down.le
  simp only [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]
  omega

/-- A floor too close to the current state forbids a first descent through time r. -/
theorem survives_of_near_floor {s w r : ℕ} (hs : s.Prime) (large : 18*11^r ≤ s)
    (floor : ∀ i ≤ r, w ≤ state s i)
    (near : 2*(10^r+1)*s < 2*(10^r+1)*w+s) : Survives s r := by
  classical
  by_contra h
  have hit : ∃ j, j ≤ r ∧ state s j < s := by simpa [Survives] using h
  let j := Nat.find hit
  have hj : j ≤ r ∧ state s j < s := Nat.find_spec hit
  have prior (i : ℕ) (hi : i < j) : s ≤ state s i :=
    le_of_not_gt fun down => Nat.find_min hit hi ⟨by omega,down⟩
  have loss := descent_gap hs hj.1 prior hj.2 large
  have lower := Nat.mul_le_mul_left (2*(10^r+1)) (floor j hj.1)
  omega

theorem state_add (p i j : ℕ) : state p (i+j) = state (state p i) j := by
  simp only [state, Nat.add_comm i j, Function.iterate_add_apply]

def UnboundedOrbit (p : ℕ) : Prop := ∀ B, ∃ n, B < state p n

theorem state_injective_of_unbounded {p : ℕ} (hu : UnboundedOrbit p) :
    Function.Injective (state p) := by
  have distinct : ∀ i j, i < j → state p i ≠ state p j := by
    intro i j hij he
    let bound := (Finset.range j).sup (state p)
    have bounded : ∀ n, state p n ≤ bound := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases before : n < j
        · exact Finset.le_sup (f := state p) (Finset.mem_range.mpr before)
        · have hn : j+(n-j) = n := by omega
          have hs : state p n = state p (i+(n-j)) := by
            calc
              state p n = state p (j+(n-j)) := congrArg (state p) hn.symm
              _ = state p (i+(n-j)) := by rw [state_add p j, state_add p i, he]
          rw [hs]
          exact ih _ (by omega)
    obtain ⟨n, hn⟩ := hu bound
    exact (not_lt_of_ge (bounded n)) hn
  intro i j equal
  rcases lt_trichotomy i j with h | h | h
  · exact (distinct i j h equal).elim
  · exact h
  · exact (distinct j i h equal.symm).elim

theorem tail_above_of_unbounded {p : ℕ} (hu : UnboundedOrbit p) (Y : ℕ) :
    ∃ N, ∀ n ≥ N, Y ≤ state p n := by
  induction Y with
  | zero => exact ⟨0, fun _ _ => Nat.zero_le _⟩
  | succ Y ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hit : ∃ z, state p z = Y
    · obtain ⟨z, hz⟩ := hit
      refine ⟨max N (z+1), fun n hn => ?_⟩
      have lower := hN n (le_trans (le_max_left ..) hn)
      have later := le_trans (le_max_right ..) hn
      have ne : state p n ≠ Y := fun h =>
        (show n ≠ z by omega) (state_injective_of_unbounded hu (h.trans hz.symm))
      omega
    · refine ⟨N, fun n hn => ?_⟩
      have lower := hN n hn
      have ne : state p n ≠ Y := fun he => hit ⟨n,he⟩
      omega

/-- Every integer window [Y,10Y) above an escaping seed contains an attained
    tail minimum whose whole forward orbit stays at or above it. -/
theorem escaping_window {p Y : ℕ} (hp : p.Prime) (hu : UnboundedOrbit p) (hY : p < Y) :
    ∃ i, Y ≤ state p i ∧ state p i < 10*Y ∧
      ∀ j, state p i ≤ state (state p i) j := by
  classical
  let h := tail_above_of_unbounded hu Y
  let N := Nat.find h
  have tail : ∀ n ≥ N, Y ≤ state p n := Nat.find_spec h
  have pos : 0 < N := by
    by_contra! hz
    have hh := tail 0 (by omega)
    simp [state] at hh
    omega
  have low : state p (N-1) < Y := by
    by_contra! high
    apply Nat.find_min h (m := N-1) (by change N-1 < N; omega)
    intro n hn
    by_cases hge : N ≤ n
    · exact tail n hge
    · have : n = N-1 := by omega
      simpa [this] using high
  have prev : N-1+1 = N := by omega
  have step : state p N = T (state p (N-1)) := by
    calc
      state p N = state p ((N-1)+1) := congrArg (state p) prev.symm
      _ = _ := Function.iterate_succ_apply' T (N-1) p
  have div := Nat.le_of_dvd (lt_trans Nat.zero_lt_one (extend_gt_one (iterate_prime hp (N-1)).pos))
    (T_dvd (iterate_prime hp (N-1)).pos)
  change T (state p (N-1)) ≤ digitExtend (state p (N-1)) at div
  have upper : state p N < 10*Y := by
    rw [step]
    unfold digitExtend lastDigit at div
    omega
  let existsVal : ∃ v, ∃ i ≥ N, state p i = v := ⟨state p N,N,le_rfl,rfl⟩
  obtain ⟨i, hi, eq⟩ := Nat.find_spec existsVal
  have minimum (n : ℕ) (hn : N ≤ n) : state p i ≤ state p n := by
    rw [eq]
    exact Nat.find_min' existsVal ⟨n,hn,rfl⟩
  refine ⟨i,tail i hi,lt_of_le_of_lt (minimum N le_rfl) upper,fun j => ?_⟩
  rw [← state_add]
  exact minimum _ (by omega)

/-- Two consecutive strict interior local minima can increase, even above 23333. -/
theorem increasing_valleys_example :
    Nat.Prime 673273 ∧ T 673273 = 23459 ∧ T 23459 = 234599 ∧ T 234599 = 38459 ∧ T 38459 = 384599 := by
  exact ⟨Certificate.primeOK_sound (by rfl),
    Certificate.edgeOK_sound (fs := [7,41,23459]) (by rfl),
    Certificate.edgeOK_sound (fs := [234599]) (by rfl),
    Certificate.edgeOK_sound (fs := [61,38459]) (by rfl),
    Certificate.edgeOK_sound (fs := [384599]) (by rfl)⟩

end PrimeDynamics
