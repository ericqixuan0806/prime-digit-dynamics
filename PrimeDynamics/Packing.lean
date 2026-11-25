import PrimeDynamics.OrbitContraction
import Mathlib.Data.List.Sort

namespace PrimeDynamics

/-- The states before time n, listed in reverse time order. -/
def visited (p : ℕ) : ℕ → List ℕ
  | 0 => []
  | i+1 => state p i :: visited p i

@[simp] theorem visited_length (p n : ℕ) : (visited p n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [visited, ih]

theorem visited_prime {p : ℕ} (hp : p.Prime) {n a : ℕ} (h : a ∈ visited p n) : a.Prime := by
  induction n with
  | zero => simp [visited] at h
  | succ n ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact iterate_prime hp n
    · exact ih ht

private def raised (xs : List ℕ) := (xs.map (·+1)).prod

private theorem raised_pos (xs : List ℕ) : 0 < raised xs := by
  induction xs with
  | nil => decide
  | cons a xs ih => exact Nat.mul_pos (Nat.succ_pos a) ih

private theorem local_spacing {b a : ℕ} (hb : 2 ≤ b) (ha : b ≤ a) :
    (b-1)*(a+1)^2 < (b+1)*a^2 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le ha
  have he : 2+u-1 = u+1 := by omega
  rw [he]
  nlinarith only [Nat.zero_le (u*v), Nat.zero_le (v^2), Nat.zero_le u, Nat.zero_le v]

private theorem sorted_packing {xs : List ℕ} {b : ℕ} (hb : 2 ≤ b)
    (hs : xs.Pairwise (· ≤ ·)) (hn : xs.Nodup)
    (hl : ∀ a ∈ xs, b ≤ a ∧ a%2=1) :
    (b-1)*(raised xs)^2 ≤ (b+2*xs.length-1)*xs.prod^2 ∧
    (xs ≠ [] → (b-1)*(raised xs)^2 < (b+2*xs.length-1)*xs.prod^2) := by
  induction xs generalizing b with
  | nil => simp [raised]
  | cons a xs ih =>
    obtain ⟨hg,ha⟩ := hl a (List.mem_cons_self ..)
    have htail : ∀ x ∈ xs, b+2 ≤ x ∧ x%2=1 := by
      intro x hx
      have hx' := hl x (List.mem_cons_of_mem _ hx)
      have hax := (List.pairwise_cons.mp hs).1 x hx
      have hne : a ≠ x := fun e => (List.nodup_cons.mp hn).1 (e ▸ hx)
      exact ⟨by omega,hx'.2⟩
    have ht := (ih (b := b+2) (by omega) (List.pairwise_cons.mp hs).2 (List.nodup_cons.mp hn).2 htail).1
    have hbp : b+2-1 = b+1 := by omega
    rw [hbp] at ht
    have hv : b+2+2*xs.length-1 = b+2*(a::xs).length-1 := by simp; omega
    have hlt : (b-1)*(raised (a::xs))^2 < (b+2*(a::xs).length-1)*(a::xs).prod^2 := by
      calc
        _ = ((b-1)*(a+1)^2)*(raised xs)^2 := by simp [raised]; ring
        _ < ((b+1)*a^2)*(raised xs)^2 :=
          Nat.mul_lt_mul_of_pos_right (local_spacing hb hg) (pow_pos (raised_pos xs) _)
        _ = a^2 * ((b+1)*(raised xs)^2) := by ring
        _ ≤ a^2 * ((b+2+2*xs.length-1)*xs.prod^2) := Nat.mul_le_mul_left _ ht
        _ = _ := by rw [hv]; simp only [List.prod_cons]; ring
    exact ⟨hlt.le, fun _ => hlt⟩

private theorem path_bound {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (M p n * state p n) * (visited p n).prod ≤ (10^n*p)*raised (visited p n) := by
  induction n with
  | zero => simp [M,state,visited,raised]
  | succ n ih =>
    have hd : digitExtend (state p n) ≤ 10 * (state p n+1) := by
      unfold digitExtend lastDigit
      omega
    calc
      _ = ((M p n * state p n) * (visited p n).prod) * (cofactor p n * state p (n+1)) := by
        rw [M,visited,List.prod_cons]; ring
      _ ≤ ((10^n*p)*raised (visited p n)) * (10*(state p n+1)) := by
        rw [step_factor hp]; exact Nat.mul_le_mul ih hd
      _ = _ := by simp [visited,raised,pow_succ]; ring

/-- The integer version of the square-root product bound for distinct preterminal states. -/
theorem distinct_prefix_bound {p n : ℕ} (hp : p.Prime) (hb : 3 ≤ p) (hnt : 0 < n)
    (hn : (visited p n).Nodup) (hl : ∀ a ∈ visited p n, p ≤ a) :
    (p-1)*(M p n * state p n)^2 < (10^n*p)^2*(p+2*n-1) := by
  let xs := visited p n
  let ys := xs.mergeSort (fun a b => decide (a≤b))
  have perm : ys.Perm xs := List.mergeSort_perm ..
  have hsort : ys.Pairwise (· ≤ ·) := List.sorted_mergeSort' (· ≤ ·) xs
  have hh := (sorted_packing (b := p) (by omega) hsort (perm.nodup_iff.mpr hn) (fun a ha => by
    have hm := perm.mem_iff.mp ha
    have hlo := hl a hm
    exact ⟨hlo,(visited_prime hp hm).eq_two_or_odd.resolve_left (by omega)⟩)).2
  have hlen : ys.length = n := perm.length_eq.trans (visited_length ..)
  have hne : ys ≠ [] := fun h => by simp [h] at hlen; omega
  have hpack := hh hne
  have hraised : raised ys = raised xs := (perm.map (fun x => x+1)).prod_eq
  rw [hlen,hraised,perm.prod_eq] at hpack
  have hpath := path_bound hp n
  change (M p n * state p n) * xs.prod ≤ (10^n*p) * raised xs at hpath
  have hpos : 0 < (10^n*p)^2 := pow_pos (Nat.mul_pos (by positivity) hp.pos) _
  have hh' : ((p-1)*(M p n*state p n)^2)*xs.prod^2 < ((10^n*p)^2*(p+2*n-1))*xs.prod^2 := by
    calc
      _ = (p-1)*((M p n*state p n)*xs.prod)^2 := by ring
      _ ≤ (p-1)*((10^n*p)*raised xs)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpath 2)
      _ = (10^n*p)^2*((p-1)*(raised xs)^2) := by ring
      _ < (10^n*p)^2*((p+2*n-1)*xs.prod^2) := Nat.mul_lt_mul_of_pos_left hpack hpos
      _ = _ := by ring
  by_contra! h
  exact (not_le_of_gt hh') (Nat.mul_le_mul_right _ h)

end PrimeDynamics
