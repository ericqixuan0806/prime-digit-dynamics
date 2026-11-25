import PrimeDynamics.Certificate
namespace PrimeDynamics
open Certificate
theorem cycle_nodup : cycle.Nodup := by decide
theorem cycle_length : cycle.length = 26 := by decide
theorem cycleEdge23 : T 23 = 233 := edgeOK_sound (fs := [233]) (by rfl)
theorem cycleEdge233 : T 233 = 2333 := edgeOK_sound (fs := [2333]) (by rfl)
theorem cycleEdge2333 : T 2333 = 23333 := edgeOK_sound (fs := [23333]) (by rfl)
theorem cycleEdge23333 : T 23333 = 661 := edgeOK_sound (fs := [353, 661]) (by rfl)
theorem cycleEdge661 : T 661 = 601 := edgeOK_sound (fs := [11, 601]) (by rfl)
theorem cycleEdge601 : T 601 = 6011 := edgeOK_sound (fs := [6011]) (by rfl)
theorem cycleEdge6011 : T 6011 = 6679 := edgeOK_sound (fs := [3, 3, 6679]) (by rfl)
theorem cycleEdge6679 : T 6679 = 997 := edgeOK_sound (fs := [67, 997]) (by rfl)
theorem cycleEdge997 : T 997 = 907 := edgeOK_sound (fs := [11, 907]) (by rfl)
theorem cycleEdge907 : T 907 = 313 := edgeOK_sound (fs := [29, 313]) (by rfl)
theorem cycleEdge313 : T 313 = 241 := edgeOK_sound (fs := [13, 241]) (by rfl)
theorem cycleEdge241 : T 241 = 2411 := edgeOK_sound (fs := [2411]) (by rfl)
theorem cycleEdge2411 : T 2411 = 47 := edgeOK_sound (fs := [3, 3, 3, 19, 47]) (by rfl)
theorem cycleEdge47 : T 47 = 53 := edgeOK_sound (fs := [3, 3, 53]) (by rfl)
theorem cycleEdge53 : T 53 = 41 := edgeOK_sound (fs := [13, 41]) (by rfl)
theorem cycleEdge41 : T 41 = 137 := edgeOK_sound (fs := [3, 137]) (by rfl)
theorem cycleEdge137 : T 137 = 17 := edgeOK_sound (fs := [3, 3, 3, 3, 17]) (by rfl)
theorem cycleEdge17 : T 17 = 59 := edgeOK_sound (fs := [3, 59]) (by rfl)
theorem cycleEdge59 : T 59 = 599 := edgeOK_sound (fs := [599]) (by rfl)
theorem cycleEdge599 : T 599 = 857 := edgeOK_sound (fs := [7, 857]) (by rfl)
theorem cycleEdge857 : T 857 = 953 := edgeOK_sound (fs := [3, 3, 953]) (by rfl)
theorem cycleEdge953 : T 953 = 9533 := edgeOK_sound (fs := [9533]) (by rfl)
theorem cycleEdge9533 : T 9533 = 13619 := edgeOK_sound (fs := [7, 13619]) (by rfl)
theorem cycleEdge13619 : T 13619 = 19457 := edgeOK_sound (fs := [7, 19457]) (by rfl)
theorem cycleEdge19457 : T 19457 = 821 := edgeOK_sound (fs := [3, 79, 821]) (by rfl)
theorem cycleEdge821 : T 821 = 23 := edgeOK_sound (fs := [3, 7, 17, 23]) (by rfl)

theorem cycle_primes : ∀ p ∈ cycle, Nat.Prime p := by
  have h : cycle.all primeOK = true := by rfl
  exact fun p hp => primeOK_sound (List.all_eq_true.mp h p hp)
end PrimeDynamics
