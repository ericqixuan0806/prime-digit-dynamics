import PrimeDynamics.AscentDigits
import Mathlib.Data.Nat.ModEq

open Finset Nat

namespace PrimeDynamics

/-- Recover the source residue of an actual digit step from its target modulo 13. -/
theorem inverse_ascent_digit_mod13 {x y u d : ℕ} (digit : d ≤ 9)
    (edge : u*y = 10*x+d) : (4*(u*(y%13)+13-d))%13 = x%13 := by
  have shift (z : ℕ) : u*z+13-d = u*z+(13-d) := by omega
  have congr : 4*(u*(y%13)+(13-d)) ≡ 4*(u*y+(13-d)) [MOD 13] :=
    ((Nat.mod_modEq y 13).mul_left u |>.add_right (13-d)).mul_left 4
  rw [shift]
  apply congr.trans
  rw [← shift,edge]
  change (4*(10*x+d+13-d))%13 = x%13
  omega

private def reverseSteps13 (y : ℕ) : List (ℕ × ℕ) → Option ℕ
  | [] => if y=0 then none else some y
  | (u,d)::rest => if y=0 then none else reverseSteps13 ((4*(u*y+13-d))%13) rest

private def reverseRun (u d k : ℕ) : List (ℕ × ℕ) := (u,d)::List.replicate k (1,d)

/-- The first two inputs count pure steps. A positive final entry selects
    the (9,7,7) word and gives its last run length, including its nonunit edge. -/
def returnSource13 (y : Fin 13) (i : Fin 2) (j : Fin 5) (k : Fin 6) : Option ℕ :=
  reverseSteps13 y.val (if k.val = 0 then reverseRun 7 9 j.val ++ reverseRun 3 7 i.val
    else reverseRun 7 9 (k.val-1) ++ reverseRun 7 3 j.val ++ reverseRun 9 7 i.val)

def returnUpper13 (x : ℕ) : ℕ := (([0,1,1,0,0,0,0,1,2,0,2,2,0] : List ℕ)[x]?).getD 0
def returnLower13 (x : ℕ) : ℕ := (([0,3,1,5,2,0,4,1,0,3,0,4,2] : List ℕ)[x]?).getD 0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- Check both inequalities on every residue and every possible return shape. -/
theorem ascent_return_cost_mod13 : ∀ (y : Fin 13) (i : Fin 2) (j : Fin 5) (k : Fin 6),
    let h := i.val+j.val+2+k.val
    let a := if k.val = 0 then 1 else 2
    (returnSource13 y i j k).all (fun x => decide (
      2*h + returnUpper13 x ≤ 13*a + returnUpper13 y.val ∧
      11*a + returnLower13 x ≤ 7*h + returnLower13 y.val)) = true := by decide

/-- Sum the two certified costs along a compatible path of returns. -/
theorem ascent_return_budget (x h a : ℕ → ℕ) (n : ℕ)
    (steps : ∀ i < n, 2*h i+returnUpper13 (x i) ≤ 13*a i+returnUpper13 (x (i+1)) ∧
      11*a i+returnLower13 (x i) ≤ 7*h i+returnLower13 (x (i+1))) :
    2*(∑ i ∈ range n, h i)+returnUpper13 (x 0) ≤
        13*(∑ i ∈ range n, a i)+returnUpper13 (x n) ∧
    11*(∑ i ∈ range n, a i)+returnLower13 (x 0) ≤
        7*(∑ i ∈ range n, h i)+returnLower13 (x n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨u,l⟩ := ih (fun i hi => steps i (by omega))
    obtain ⟨u',l'⟩ := steps n (by omega)
    simp only [sum_range_succ]
    omega

end PrimeDynamics
