-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionClosedBandGraph
public import SlowEquilibration.SphericalFiniteCritical

@[expose] public section

/-! Almost-sure finiteness of the literal reduction centers under the
original mixed Gaussian tensor law. -/

namespace SlowEquilibration.SourceReductionFiniteCentersAE
noncomputable section
open MeasureTheory SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalMorse SourceReductionClosedBandGraph
open scoped RealInnerProductSpace
set_option autoImplicit false

theorem windowCenters_finite_ae (d : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (m M : ℝ) (U : Set ℝ) :
    ∀ᵐ J ∂disorderLaw (d+2) μ.maxDegree,
      (windowCenters (N := d+2) μ Q m M U J).Finite := by
  have h := actual_sphere_criticalSet_finite_ae (d+1) (by omega) μ hQ
  filter_upwards [h] with J hJ
  apply hJ.subset
  intro u hu
  change (J,u) ∈ windowCenterGraph μ Q m M U at hu
  unfold windowCenterGraph at hu
  exact ⟨hu.1.1.1,hu.1.1.2⟩

end
end SlowEquilibration.SourceReductionFiniteCentersAE
