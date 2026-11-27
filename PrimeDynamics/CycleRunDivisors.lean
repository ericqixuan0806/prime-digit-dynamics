import PrimeDynamics.RecordProducts
import PrimeDynamics.SingleReduction
import Mathlib.Data.Nat.ModEq

open Nat

namespace PrimeDynamics

theorem actual_pure_prefix {p : ℕ} (hp : p.Prime) (k : ℕ)
    (units : ∀ i < k, cofactor p i = 1) :
    state p k = pureRun p k ∧ M p k = 1 := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    obtain ⟨path,prod⟩ := ih (fun i hi => units i (by omega))
    have edge := step_factor hp k
    rw [units k (by omega),one_mul,path] at edge
    exact ⟨edge,by rw [M,prod,units k (by omega),one_mul]⟩

theorem actual_run_edge {p : ℕ} (hp : p.Prime) (k : ℕ)
    (units : ∀ i < k, cofactor p i = 1) :
    M p (k+1) * state p (k+1) = 10^(k+1)*p + lastDigit p * repunit (k+1) := by
  obtain ⟨path,prod⟩ := actual_pure_prefix hp k units
  rw [M,prod,one_mul,step_factor hp,path,← pureRun_affine]
  rfl

/-- Each entry counts pure steps before the final edge of one block. -/
def runLength : List ℕ → ℕ
  | [] => 0
  | k :: ks => (k+1) + runLength ks

def runDivisors (g p : ℕ) : List ℕ → Prop
  | [] => True
  | k :: ks => (∀ i < k, cofactor p i = 1) ∧ g ∣ lastDigit p * repunit (k+1) ∧
      runDivisors g (state p (k+1)) ks

private theorem compose_run_congruences {g u v A B x y z : ℕ}
    (first : u*y ≡ A*x [MOD g]) (second : v*z ≡ B*y [MOD g]) :
    u*v*z ≡ A*B*x [MOD g] := by
  calc
    u*v*z = u*(v*z) := by ring
    _ ≡ u*(B*y) [MOD g] := second.mul_left u
    _ = B*(u*y) := by ring
    _ ≡ B*(A*x) [MOD g] := first.mul_left B
    _ = _ := by ring

theorem actual_run_congruence {p g : ℕ} (hp : p.Prime) (ks : List ℕ)
    (blocks : runDivisors g p ks) :
    M p (runLength ks)*state p (runLength ks) ≡ 10^(runLength ks)*p [MOD g] := by
  induction ks generalizing p with
  | nil => change 1*p ≡ 1*p [MOD g]; rfl
  | cons k ks ih =>
    obtain ⟨units,divisor,rest⟩ := blocks
    have first : M p (k+1)*state p (k+1) ≡ 10^(k+1)*p [MOD g] := by
      rw [actual_run_edge hp k units]
      simpa using divisor.modEq_zero_nat.add_left (10^(k+1)*p)
    have second := ih (iterate_prime hp (k+1)) rest
    rw [runLength,cofactor_product_append p (k+1) (runLength ks),
      state_add p (k+1) (runLength ks),pow_add]
    exact compose_run_congruences first second

private theorem gap_at_state {g P A u : ℕ} (le : A ≤ u) (rel : u*P ≡ A*P [MOD g]) :
    g ∣ (u-A)*P := by
  rw [Nat.sub_mul]
  exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right P le)).mp rel.symm

/-- Split a genuine closed orbit at two different prime states. Each side may
    contain arbitrarily many blocks. The common divisor divides the cycle excess. -/
theorem actual_cycle_run_divisor {p g : ℕ} (hp : p.Prime) (left right : List ℕ)
    (first : runDivisors g p left)
    (second : runDivisors g (state p (runLength left)) right)
    (close : state p (runLength left + runLength right) = p)
    (distinct : state p (runLength left) ≠ p) :
    g ∣ M p (runLength left + runLength right) - 10^(runLength left + runLength right) := by
  let a := runLength left
  let b := runLength right
  let q := state p a
  have hq : q.Prime := iterate_prime hp a
  have back : state q b = p := (state_add p a b).symm.trans close
  have f := actual_run_congruence hp left first
  have s := actual_run_congruence hq right second
  change M p a*q ≡ 10^a*p [MOD g] at f
  change M q b*state q b ≡ 10^b*q [MOD g] at s
  rw [back] at s
  change g ∣ M p (a+b) - 10^(a+b)
  rw [cofactor_product_append,pow_add]
  change g ∣ M p a*M q b - 10^a*10^b
  by_cases le : 10^a*10^b ≤ M p a*M q b
  · have atP := gap_at_state le (compose_run_congruences f s)
    have atQ := gap_at_state le (show M p a*M q b*q ≡ 10^a*10^b*q [MOD g] by
      simpa only [Nat.mul_comm (M q b) (M p a),Nat.mul_comm (10^b) (10^a)] using
        compose_run_congruences s f)
    have cop : p.Coprime q := hp.coprime_iff_not_dvd.mpr (fun hit => by
      rcases (Nat.dvd_prime hq).mp hit with one | eq
      · exact hp.ne_one one
      · exact distinct eq.symm)
    simpa only [Nat.gcd_mul_left,cop.gcd_eq_one,Nat.mul_one] using Nat.dvd_gcd atP atQ
  · simp [Nat.sub_eq_zero_of_le (le_of_not_ge le)]

/-- Two reductions after h and k pure prefix edges, expressed directly with T iterates. -/
theorem actual_two_run_gap {p h k : ℕ} (hp : p.Prime)
    (first : ∀ i < h, cofactor p i = 1)
    (second : ∀ i < k, cofactor (state p (h+1)) i = 1)
    (close : state p ((h+1)+(k+1)) = p) (distinct : state p (h+1) ≠ p) :
    Nat.gcd (lastDigit p * repunit (h+1)) (lastDigit (state p (h+1)) * repunit (k+1)) ∣
      M p ((h+1)+(k+1)) - 10^((h+1)+(k+1)) := by
  apply actual_cycle_run_divisor hp [h] [k]
  · exact ⟨first,Nat.gcd_dvd_left _ _,trivial⟩
  · exact ⟨second,Nat.gcd_dvd_right _ _,trivial⟩
  · exact close
  · exact distinct

end PrimeDynamics
