-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalResidualOriginalIntegral

@[expose] public section

/-! The literal central latitude partition and normalized residual partition
are related by the original conditioned energy and annealed factors. This is
the scalar identity used after latitude averaging in manuscript §12.20. -/

namespace SlowEquilibration.SphericalTAPCriticalBand
noncomputable section
open MeasureTheory Set SphericalModel SphericalGaussianJet
set_option autoImplicit false
set_option maxHeartbeats 400000

def originalCriticalLatitudePartition (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (β : ℝ)
    (J : Disorder (n+1) μ.maxDegree) : ℝ :=
  ∫ ω : Vector (n+1),
    Real.exp (β*field (mixtureCoefficients μ) J (Real.sqrt Q • (u+ω)))
      ∂criticalTransverseOffsetLaw n Q e

/-- Source equation `mb-section` at the partition level: the original
central latitude integral is the conditioned center factor times the
annealed residual factor times the genuinely normalized integral. -/
theorem originalCriticalTransverseNormalizedPartition_eq_latitude
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (β e₀ : ℝ) (J : Disorder (n+1) μ.maxDegree) :
    originalCriticalTransverseNormalizedPartition n μ hQ u e β e₀ J =
      Real.exp (-(((n+1:ℕ):ℝ)*β^2*
        (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2+
          β*(((n+1:ℕ):ℝ)*e₀))) *
        originalCriticalLatitudePartition n μ Q u e β J := by
  let A := ((n+1:ℕ):ℝ)*β^2*
    (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2
  let m := ((n+1:ℕ):ℝ)*e₀
  let H : Vector (n+1) → ℝ := fun ω =>
    field (mixtureCoefficients μ) J (Real.sqrt Q • (u+ω))
  unfold originalCriticalTransverseNormalizedPartition originalCriticalLatitudePartition
  dsimp only
  change Real.exp (-((n+1:ℕ):ℝ)*β^2*
      (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi 1/2)*
      (∫ ω, Real.exp (β*(H ω-m)) ∂criticalTransverseOffsetLaw n Q e) =
    Real.exp (-(A+β*m))*
      (∫ ω, Real.exp (β*H ω) ∂criticalTransverseOffsetLaw n Q e)
  have he (ω : Vector (n+1)) :
      Real.exp (β*(H ω-m)) = Real.exp (-β*m)*Real.exp (β*H ω) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simp_rw [he, integral_const_mul]
  rw [←mul_assoc, ←Real.exp_add]
  congr 1
  dsimp [A]
  push_cast
  ring

end
end SlowEquilibration.SphericalTAPCriticalBand
