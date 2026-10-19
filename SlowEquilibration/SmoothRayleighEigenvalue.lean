-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SmoothRayleighTrialLower

/-! Exact equality between the standard smooth Rayleigh min-max value and
the ordered eigenvalues of the constructed spherical Gibbs generator. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PalomarCusp
open MeasureTheory Set
open SphericalModel SphericalForm SphericalSpectralComparison
set_option maxHeartbeats 600000
variable {N : ℕ}

lemma literal_rayleigh_le_of_trial {π : Measure (Vector N)} {k : ℕ} {b : ℝ}
    (ht : SlowEquilibrationCuspSource.RayleighTrial π k b) :
    SlowEquilibrationCuspSource.rayleighEigenvalue π k≤b := by
  exact csInf_le ⟨0,fun _ hb => literal_trial_nonneg hb⟩ ht

/-- This standard, literal smooth min-max formula gives the actual spectrum;
the proof derives both inequalities from the completed form and its dense
smooth core, and makes no attainment or smooth-eigenfunction assumption. -/
theorem literal_rayleigh_eq_eigenvalue (hN : 2≤N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (D : SphericalSpectralData hN β H hH.continuous) (k : ℕ) :
    SlowEquilibrationCuspSource.rayleighEigenvalue (gibbsLaw N β H) k=D.eigenvalue k := by
  have htrial (b : ℝ) (hb : D.eigenvalue k<b) :
      SlowEquilibrationCuspSource.RayleighTrial (gibbsLaw N β H) k b :=
    core_trial_representation (show 1≤N by omega) β hH k b
      (exists_smooth_trial_above_eigenvalue hN β hH D k b hb)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact literal_rayleigh_le_of_trial (htrial (D.eigenvalue k+ε) (by linarith))
  · apply le_csInf
    · exact ⟨D.eigenvalue k+1,htrial (D.eigenvalue k+1) (by linarith)⟩
    · intro b hb
      exact literal_trial_eigenvalue_le hN β hH D k b hb

end SlowEquilibration.PalomarCusp
