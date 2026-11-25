import PrimeDynamics.SurvivalWindows

namespace PrimeDynamics

def recip (a : ℕ) : ℚ := 1 / (a : ℚ)

noncomputable def survivalWeight (r a : ℕ) : ℚ := by
  classical
  exact if Survives a r then recip a else 0

def windowCost (r : ℕ) := 2*r*(10^r+1)

private theorem recip_nonneg (a : ℕ) : 0 ≤ recip a := by
  by_cases h : a = 0
  · simp [recip,h]
  · exact (one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero h : (0:ℚ) < a)).le

private theorem recip_antitone {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : recip b ≤ recip a := by
  apply (div_le_div_iff₀ (by exact_mod_cast ha.trans_le hab : (0:ℚ) < b)
    (by exact_mod_cast ha : (0:ℚ) < a)).mpr
  simpa using (show (a:ℚ) ≤ b by exact_mod_cast hab)

private theorem survivalWeight_nonneg (r a : ℕ) : 0 ≤ survivalWeight r a := by
  classical
  unfold survivalWeight
  split
  · exact recip_nonneg a
  · rfl

private theorem orbitSum_nonneg {f : ℕ → ℚ} (hf : ∀ a, 0 ≤ f a) (p n : ℕ) :
    0 ≤ orbitSum f p n := by
  induction n with
  | zero => rfl
  | succ n ih => exact add_nonneg ih (hf _)

private theorem orbitSum_one (f : ℕ → ℚ) (p : ℕ) : orbitSum f p 1 = f p := by
  simp [orbitSum,state]

theorem orbitSum_append (f : ℕ → ℚ) (p i j : ℕ) :
    orbitSum f p (i+j) = orbitSum f p i + orbitSum f (state p i) j := by
  induction j with
  | zero => simp [orbitSum]
  | succ j ih =>
    change orbitSum f p (i+j) + f (state p (i+j)) =
      orbitSum f p i + (orbitSum f (state p i) j + f (state (state p i) j))
    rw [ih,state_add p i j,add_assoc]

private theorem orbitSum_cap {f : ℕ → ℚ} {p n : ℕ} {w : ℚ} (h : ∀ i < n, f (state p i) ≤ w) :
    orbitSum f p n ≤ (n:ℚ)*w := by
  induction n with
  | zero => simp [orbitSum]
  | succ n ih =>
    have earlier := ih (fun i hi => h i (by omega))
    simpa [orbitSum,add_mul] using add_le_add earlier (h n (by omega))

private theorem pay_descent {p q j r : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hqp : q ≤ p) (hjr : j ≤ r)
    (gap : 2*(10^r+1)*q + p ≤ 2*(10^r+1)*p) :
    (j:ℚ)*recip p + (windowCost r:ℚ)*recip p ≤ (windowCost r:ℚ)*recip q := by
  have cross : (j+windowCost r)*q ≤ windowCost r*p := calc
    (j+windowCost r)*q = windowCost r*q+j*q := by ring
    _ ≤ windowCost r*q+r*p := Nat.add_le_add_left (Nat.mul_le_mul hjr hqp) _
    _ = r*(2*(10^r+1)*q+p) := by unfold windowCost; ring
    _ ≤ r*(2*(10^r+1)*p) := Nat.mul_le_mul_left r gap
    _ = windowCost r*p := by unfold windowCost; ring
  rw [← add_mul]
  simp only [recip, ← mul_div_assoc, mul_one]
  exact (div_le_div_iff₀ (by exact_mod_cast hp) (by exact_mod_cast hq)).mpr (by exact_mod_cast cross)

/-- Either one survival step is charged, or a first-descent block pays for itself. -/
theorem payable_window {p r : ℕ} (hp : p.Prime) (hr : 0 < r) (large : 18*11^r ≤ p) :
    ∃ j, 0 < j ∧ j ≤ r ∧ orbitSum recip p j + (windowCost r:ℚ)*recip p ≤
      (windowCost r:ℚ)*recip (state p j) + ((windowCost r:ℚ)+1)*orbitSum (survivalWeight r) p j := by
  classical
  by_cases survives : Survives p r
  · refine ⟨1,by decide,hr,?_⟩
    have he : survivalWeight r p = recip p := by simp [survivalWeight,survives]
    rw [orbitSum_one,orbitSum_one,he]
    have h := mul_nonneg (Nat.cast_nonneg (α := ℚ) (windowCost r)) (recip_nonneg (state p 1))
    linarith
  · have hit : ∃ j, j ≤ r ∧ state p j < p := by simpa [Survives] using survives
    let j := Nat.find hit
    have hj : j ≤ r ∧ state p j < p := Nat.find_spec hit
    have pos : 0 < j := by
      by_contra! small
      have eq : j = 0 := by omega
      simpa [eq,state] using hj.2
    have prior (i : ℕ) (hi : i < j) : p ≤ state p i :=
      le_of_not_gt fun down => Nat.find_min hit hi ⟨by omega,down⟩
    have bound := orbitSum_cap (f := recip) (fun i hi => recip_antitone hp.pos (prior i hi))
    have paid := pay_descent (q := state p j) hp.pos (iterate_prime hp j).pos hj.2.le hj.1
      (descent_gap hp hj.1 prior hj.2 large)
    have nonneg := mul_nonneg (show (0:ℚ) ≤ (windowCost r:ℚ)+1 by positivity)
      (orbitSum_nonneg (survivalWeight_nonneg r) p j)
    exact ⟨j,pos,hj.1,by linarith⟩

/-- Any length, including a final incomplete window. The right side counts occurrences;
    on a distinct prefix each surviving prime is charged at most once. -/
theorem finite_window_budget {p n r Y : ℕ} (hp : p.Prime) (hr : 0 < r)
    (large : 18*11^r ≤ Y) (above : ∀ i ≤ n, Y ≤ state p i) :
    orbitSum recip p n + (windowCost r:ℚ)*recip p ≤
      ((windowCost r:ℚ)+r)*recip Y + ((windowCost r:ℚ)+1)*orbitSum (survivalWeight r) p n := by
  have floorPos : 0 < Y := lt_of_lt_of_le (by positivity) large
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    have start : Y ≤ p := by simpa [state] using above 0 (Nat.zero_le n)
    by_cases short : n < r
    · have hsum := orbitSum_cap (f := recip) (fun i hi => recip_antitone floorPos (above i hi.le))
      have cost := mul_le_mul_of_nonneg_left (recip_antitone floorPos start)
        (Nat.cast_nonneg (α := ℚ) (windowCost r))
      have len := mul_le_mul_of_nonneg_right (show (n:ℚ) ≤ r by exact_mod_cast short.le) (recip_nonneg Y)
      have nonneg := mul_nonneg (show (0:ℚ) ≤ (windowCost r:ℚ)+1 by positivity)
        (orbitSum_nonneg (survivalWeight_nonneg r) p n)
      linarith
    · obtain ⟨j,pos,hj,paid⟩ := payable_window hp hr (large.trans start)
      have splitN : j+(n-j) = n := by omega
      have rest := ih (n-j) (by omega) (p := state p j) (iterate_prime hp j) (fun i hi => by
        rw [← state_add]
        exact above _ (by omega))
      have sums (f : ℕ → ℚ) : orbitSum f p n = orbitSum f p j + orbitSum f (state p j) (n-j) :=
        (congrArg (orbitSum f p) splitN).symm.trans (orbitSum_append f p j (n-j))
      rw [sums recip, sums (survivalWeight r), mul_add]
      linarith

end PrimeDynamics
