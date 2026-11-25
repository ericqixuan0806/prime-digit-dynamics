import PrimeDynamics.CertificateReplay
import PrimeDynamics.Cycle

namespace PrimeDynamics
open Certificate Certificate.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem finiteBase_verified : FiniteBase := by
  intro p hp hsmall
  apply covered_prime (w := witness p) hp (reaches_of_rows (B := 4096) ?_)
  · have h := block_sound (m := p) coverage_checked (Nat.zero_le _) (by norm_num; omega)
    simpa [checkedCover, hsmall] using h
  · intro i hi
    exact block_sound rows_checked (Nat.zero_le _) hi

theorem finiteDescent_iff_globalAttraction : FiniteDescent ↔ GlobalAttraction :=
  finiteDescent_iff_globalAttraction_of_base finiteBase_verified

end PrimeDynamics
