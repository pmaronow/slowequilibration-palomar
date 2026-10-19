-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOESpectralScale
public import SlowEquilibration.GOEClippedResolventUniform

/-! Actual physical clipped GOE trace scaling. The physical cutoff is
shown explicitly as a times the standard cutoff. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK GOEScaling
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def physicalClippedTrace (n : ℕ) (k ρ : ℝ) (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  (∑ i,(max ρ (k-eigenvalues n W i))⁻¹)/(n+1)

lemma physicalClippedTrace_eq_standard (n : ℕ) (k ρ : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    physicalClippedTrace n k ρ W=clippedResolvent n (k-2) ρ W := by
  unfold physicalClippedTrace clippedResolvent
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  ring

lemma physicalClippedTrace_measurable (n : ℕ) (k ρ : ℝ) : Measurable (physicalClippedTrace n k ρ) := by
  have he : physicalClippedTrace n k ρ=clippedResolvent n (k-2) ρ := by funext W;exact physicalClippedTrace_eq_standard n k ρ W
  rw [he]
  exact clippedResolvent_measurable n (k-2) ρ

/-- Pointwise actual physical matrix trace scales with its literal cutoff;
no marginal-law replacement or assumed eigenvalue scaling is used. -/
theorem physicalClippedTrace_scale (n : ℕ) {a : ℝ} (ha : 0 < a) (k ρ : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    physicalClippedTrace n k (a*ρ) (a • W)=a⁻¹*clippedResolvent n (k/a-2) ρ W := by
  unfold physicalClippedTrace clippedResolvent
  rw [eigenvalues_spectral_sum_scale n a W (fun z=>(max (a*ρ) (k-z))⁻¹)]
  have hentry (z:ℝ) : (max (a*ρ) (k-a*z))⁻¹=a⁻¹*(max ρ (2+(k/a-2)-z))⁻¹ := by
    have hmax : max (a*ρ) (k-a*z)=a*max ρ (k/a-z) := by
      rw [mul_max_of_nonneg ρ (k/a-z) ha.le]
      congr 1
      field_simp
    rw [hmax,mul_inv_rev]
    have hs : 2+(k/a-2)-z=k/a-z := by ring
    rw [hs]
    ring
  simp only [hentry,← Finset.mul_sum]
  ring

end
end SlowEquilibration.GOEClippedResolvent
