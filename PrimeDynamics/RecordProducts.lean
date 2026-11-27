import PrimeDynamics.SurvivalWindows
import Mathlib.Tactic.FieldSimp

namespace PrimeDynamics

theorem cofactor_shift (p i j : ℕ) : cofactor p (i+j) = cofactor (state p i) j := by
  unfold cofactor
  rw [state_add p i j, Nat.add_assoc, state_add p i (j+1)]

theorem cofactor_product_append (p i j : ℕ) : M p (i+j) = M p i * M (state p i) j := by
  induction j with
  | zero => simp [M]
  | succ j ih =>
    change M p (i+j) * cofactor p (i+j) = M p i * (M (state p i) j * cofactor (state p i) j)
    rw [ih,cofactor_shift,Nat.mul_assoc]

def dropChain (p : ℕ) : List ℕ → Prop
  | [] => True
  | t :: ts => state p t < p ∧ dropChain (state p t) ts

def dropFactors (p : ℕ) : List ℕ → ℚ
  | [] => 1
  | t :: ts => (1 + ((M p t - 10^t : ℕ) : ℚ)/(10:ℚ)^t) * dropFactors (state p t) ts

/-- Exact factorization for any list of consecutive record descents. -/
theorem drop_factorization {p : ℕ} (hp : p.Prime) {ts : List ℕ} (h : dropChain p ts) :
    (M p ts.sum : ℚ) / (10:ℚ)^ts.sum = dropFactors p ts := by
  induction ts generalizing p with
  | nil => simp [dropFactors,M]
  | cons t ts ih =>
    obtain ⟨down, rest⟩ := h
    have excess : 10^t < M p t := lt_of_not_ge fun small =>
      (Nat.not_lt.mpr (no_descent_before_crossing hp small)) down
    have tail := ih (p := state p t) (iterate_prime hp t) rest
    simp only [List.sum_cons, cofactor_product_append, Nat.cast_mul, pow_add, dropFactors]
    rw [← tail, Nat.cast_sub excess.le, Nat.cast_pow, Nat.cast_ofNat]
    field_simp

/-- Multiplication by 91 inverts the duplicated units digit modulo 100. -/
theorem recover_last_digit (a : ℕ) : (91 * digitExtend a) % 100 = lastDigit a := by
  unfold digitExtend lastDigit
  omega

private theorem small_scaled_digit {a m : ℕ} (hm : m ≤ 9) :
    (91 * (digitExtend a*m)) % 100 = lastDigit a*m := by
  have hd : lastDigit a ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  have hb := Nat.mul_le_mul hd hm
  rw [← Nat.mul_assoc, Nat.mul_mod, recover_last_digit, Nat.mod_eq_of_lt (by omega : m < 100),
    Nat.mod_eq_of_lt (by omega : lastDigit a*m < 100)]

/-- Retains the greatest-prime-factor condition for mixed words, including descents. -/
theorem cofactor_edge_iff {p m q : ℕ} (hp : 0 < p) (hq : q.Prime) (fac : digitExtend p = m*q) :
    T p = q ↔ ∀ l, l.Prime → l ∣ m → l ≤ q := by
  have qdiv : q ∣ digitExtend p := by rw [fac]; exact dvd_mul_left q m
  constructor
  · intro edge l hl hd
    rw [← edge]
    exact le_largestPrimeFactor (extend_gt_one hp) hl (fac ▸ dvd_mul_of_dvd_left hd q)
  · intro greatest
    apply le_antisymm _ (le_largestPrimeFactor (extend_gt_one hp) hq qdiv)
    have hd := T_dvd hp
    rw [fac] at hd
    rcases (T_prime hp).dvd_mul.mp hd with hm | h
    · exact greatest _ (T_prime hp) hm
    · exact Nat.le_of_dvd hq.pos h

/-- On primes at least eleven, every target has at most one smaller prime predecessor. -/
theorem ascending_predecessor_unique {a b q : ℕ} (ha : a.Prime) (hb : b.Prime)
    (la : 11 ≤ a) (lb : 11 ≤ b) (ea : T a = q) (eb : T b = q)
    (ua : a < q) (ub : b < q) : a = b := by
  obtain ⟨_,m,hm,em⟩ := (ascent_iff ha la).mp ⟨ea,ua⟩
  obtain ⟨_,n,hn,en⟩ := (ascent_iff hb lb).mp ⟨eb,ub⟩
  have mc : m = 1 ∨ m = 3 ∨ m = 7 ∨ m = 9 := by simpa using hm
  have nc : n = 1 ∨ n = 3 ∨ n = 7 ∨ n = 9 := by simpa using hn
  have scaled : digitExtend a*n = digitExtend b*m := by rw [em,en]; ring
  have hd := congrArg (fun z => (91*z)%100) scaled
  change (91 * (digitExtend a*n)) % 100 = (91 * (digitExtend b*m)) % 100 at hd
  rw [small_scaled_digit (by omega), small_scaled_digit (by omega)] at hd
  unfold digitExtend at scaled
  have prod : a*n = b*m := by
    simp only [Nat.add_mul, Nat.mul_assoc] at scaled
    omega
  have divides : a ∣ b*m := ⟨n,prod.symm⟩
  rcases ha.dvd_mul.mp divides with h | h
  · rcases (Nat.dvd_prime hb).mp h with h | h
    · omega
    · exact h
  · have := Nat.le_of_dvd (by omega : 0 < m) h
    omega

/-- Consecutive endpoint differences of repeated affine words form an exact
    geometric progression after clearing denominators. -/
theorem affine_repeat_gap (m A C : ℤ) (x : ℕ → ℤ) (k : ℕ)
    (step : ∀ i ≤ k, m*x (i+1) = A*x i+C) :
    m^k*(x (k+1)-x k) = A^k*(x 1-x 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have old := ih (fun i hi => step i (by omega))
    have next : m*(x (k+1+1)-x (k+1)) = A*(x (k+1)-x k) := by
      linarith only [step (k+1) le_rfl,step k (by omega)]
    calc
      _ = m^k*(m*(x (k+1+1)-x (k+1))) := by rw [pow_succ]; ring
      _ = A*(m^k*(x (k+1)-x k)) := by rw [next]; ring
      _ = _ := by rw [old,pow_succ]; ring

/-- Equal cofactors alone do not identify a repeated affine word. -/
theorem two_sevens_digit_change :
    Nat.Prime 30781 ∧ T 30781 = 43973 ∧ T 43973 = 62819 ∧ (43973-30781)%7 = 4 := by
  exact ⟨Certificate.primeOK_sound (by rfl),
    Certificate.edgeOK_sound (fs := [7,43973]) (by rfl),
    Certificate.edgeOK_sound (fs := [7,62819]) (by rfl),by decide⟩

/-- The entire product transports the last digit, including across descent steps. -/
theorem product_last_digit {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (M p n * state p n) % 10 = p % 10 := by
  induction n with
  | zero => simp [M,state]
  | succ n ih =>
    rw [M,Nat.mul_assoc,step_factor hp,digitExtend,Nat.mul_add]
    have dvd : 10 ∣ M p n * (10 * state p n) :=
      dvd_mul_of_dvd_right (dvd_mul_right 10 _) _
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd dvd, Nat.zero_add]
    simpa [lastDigit,Nat.mul_mod] using ih

/-- Any prime dividing a full cofactor word occurs at an edge whose true
    successor is at least that prime. -/
theorem product_prime_witness {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (n : ℕ)
    (hit : q ∣ M p n) : ∃ i < n, q ∣ cofactor p i ∧ q ≤ state p (i+1) := by
  induction n with
  | zero => simp [M,hq.not_dvd_one] at hit
  | succ n ih =>
    rcases hq.dvd_mul.mp hit with earlier | last
    · obtain ⟨i,hi,witness⟩ := ih earlier
      exact ⟨i,by omega,witness⟩
    · have edge := step_factor hp n
      have divides := dvd_mul_of_dvd_left last (state p (n+1))
      rw [edge] at divides
      have upper := le_largestPrimeFactor (extend_gt_one (iterate_prime hp n).pos) hq divides
      exact ⟨n,by omega,last,by simpa [state,Function.iterate_succ_apply',T] using upper⟩

theorem intercept_pos {p : ℕ} (hp : p.Prime) (large : 11 ≤ p) (n : ℕ) :
    0 < C p (n+1) := by
  induction n with
  | zero =>
    change 0 < 10*0 + (p%10)*1
    have hpos : p%10 ≠ 0 := by
      intro hz
      rcases (Nat.dvd_prime hp).mp (Nat.dvd_iff_mod_eq_zero.mpr hz) with eq | eq <;> omega
    omega
  | succ n ih =>
    rw [C]
    omega

/-- At minimal integer excess, a descending word has equal terminal digits,
    and its endpoint strictly exceeds ten times the equal-length power of ten. -/
theorem unit_excess_endpoint {p t : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (ends : state p t < p) (unit : M p t = 10^t+1) :
    state p t % 10 = p % 10 ∧ 10^(t+1) < state p t := by
  cases t with
  | zero => simp [state] at ends
  | succ n =>
    have digits := product_last_digit hp (n+1)
    rw [unit, pow_succ] at digits
    have same : state p (n+1) % 10 = p % 10 := by
      have reord : (10^n*10+1)*state p (n+1) = 10*(10^n*state p (n+1))+state p (n+1) := by ring
      rw [reord] at digits
      omega
    have gap : state p (n+1) + 10 ≤ p := by omega
    have first := intercept_pos hp large n
    have affine := affine_identity hp (n+1)
    rw [unit,Nat.add_mul,one_mul] at affine
    have scaled := Nat.mul_le_mul_left (10^(n+1)) gap
    rw [Nat.mul_add] at scaled
    exact ⟨same,by rw [pow_succ (10:ℕ) (n+1)]; omega⟩

/-- Every ascent above the one-digit primes has growth at least ten ninths. -/
theorem ascent_minimum_growth {p q : ℕ} (hp : p.Prime) (large : 11 ≤ p)
    (step : T p = q) (up : p < q) : 10*p ≤ 9*q := by
  obtain ⟨_,m,mem,fac⟩ := (ascent_iff hp large).mp ⟨step,up⟩
  have hm : m=1 ∨ m=3 ∨ m=7 ∨ m=9 := by simpa using mem
  have bound := Nat.mul_le_mul_right q (show m ≤ 9 by omega)
  unfold digitExtend at fac
  omega

/-- At excess nine the order is attached to 10/3 modulo 109, rather than 10. -/
theorem square_excess_order_example :
    Nat.Prime 53639 ∧ T 53639 = 536399 ∧ T 536399 = 49211 ∧
    10^4 % 109 = 81 ∧ 3*76 % 109 = 10 ∧ 76^2 % 109 = 108 := by
  exact ⟨Certificate.primeOK_sound (by rfl),
    Certificate.edgeOK_sound (fs := [536399]) (by rfl),
    Certificate.edgeOK_sound (fs := [109,49211]) (by rfl),by decide,by decide,by decide⟩

end PrimeDynamics
