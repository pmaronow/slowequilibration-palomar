-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorResidualLaw

@[expose] public section

/-! Every genuine affine critical-point posterior has the exact whole-field
law of the independent physical finite Taylor-residual mixture. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.SphericalLatitudeChartKacRice
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [SecondCountableTopology K] [T2Space K] [Nonempty K]

theorem latitude_posterior_transverse_residualLaw {n d : ℕ} (hd : 0<d) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q∈Set.Ioo (0 : ℝ) 1) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ y,inner ℝ (e y) w=0)
    {q : ℝ} (hq : |q|≤1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (l : Vector d →ₗᵢ[ℝ] Vector (n+2)) (hl : ∀ z,inner ℝ (l z) (latitudeMap w e q y)=0)
    (x : K → Vector d) (hx : Continuous x)
    (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let θ := μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    let z := fun u => transverseOffset l Q (x u)
    let hz : Continuous z := transverseOffset_parameter_continuous l Q x hx
    (coefficientKernel (latitudeJointCLM c w e q y hy) target).map
      (fun J => taylorContinuousField c (latitudeMap w e q y) z hz (euclideanDisorder J))=
    (disorderLaw d θ.maxDegree).map
      (fun J => Real.sqrt (((n+2 : ℕ) : ℝ)/(d : ℝ)) •
        modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let z := fun u => transverseOffset l Q (x u)
  have hz : Continuous z := transverseOffset_parameter_continuous l Q x hx
  have ht : ∀ u,inner ℝ (z u) (latitudeMap w e q y)=0 :=
    fun u => transverseOffset_tangent _ l hl Q (x u)
  exact (latitude_posterior_taylorContinuousField_map c
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.1.le)
    w e q y hy z hz ht target).trans
      (transverse_taylorContinuousField_law (by omega) hd μ hQ _
        (latitudeMap_norm_sq (by omega) w hw e he hq y hy) l hl x hx)

end
end SlowEquilibration.SphericalTaylorRemainder
