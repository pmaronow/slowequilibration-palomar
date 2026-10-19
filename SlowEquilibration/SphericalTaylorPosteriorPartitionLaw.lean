-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorPosteriorResidualLaw
public import SlowEquilibration.ContinuousFieldPartition

@[expose] public section

/-! The literal transverse partition under the genuine first-jet posterior
has the actual residual model's pressure law at the corrected temperature. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.SphericalLatitudeChartKacRice
open SlowEquilibration.ContinuousFieldLaw
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

omit [CompactSpace K] [BorelSpace K] in
theorem compact_logPartition_smul (ν : Measure K) (β s : ℝ) (f : C(K,ℝ)) :
    ContinuousFieldPartition.logPartition ν β (s • f)=
      ContinuousFieldPartition.logPartition ν (β*s) f := by
  unfold ContinuousFieldPartition.logPartition ContinuousFieldPartition.partition
  congr 1
  apply integral_congr_ae
  exact .of_forall (fun x => by simp only [ContinuousMap.smul_apply,smul_eq_mul]; congr 1; ring)

/-- Actual every-target posterior pressure-law identity; its temperature
and normalization are the physical sqrt(N/d) and 1/N factors. -/
theorem latitude_posterior_transverse_logPartition_law {n d : ℕ} (hd : 0<d)
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (ν : Measure K) [IsProbabilityMeasure ν] (β : ℝ) (μ : FiniteMixture)
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
      (fun J => ContinuousFieldPartition.logPartition ν β
        (taylorContinuousField c (latitudeMap w e q y) z hz (euclideanDisorder J))/((n+2 : ℕ) : ℝ))=
    (disorderLaw d θ.maxDegree).map
      (fun J => ContinuousFieldPartition.logPartition ν (β*Real.sqrt (((n+2 : ℕ) : ℝ)/(d : ℝ)))
        (modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J))/((n+2 : ℕ) : ℝ)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let θ := μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
  let z := fun u => transverseOffset l Q (x u)
  have hz : Continuous z := transverseOffset_parameter_continuous l Q x hx
  let X := fun J => taylorContinuousField c (latitudeMap w e q y) z hz (euclideanDisorder J)
  let Y := fun J : Disorder d θ.maxDegree => Real.sqrt (((n+2 : ℕ) : ℝ)/(d : ℝ)) •
    modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)
  have hX : Measurable X := (taylorContinuousField c (latitudeMap w e q y) z hz).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  have hY : Measurable Y := ((modelContinuousField (mixtureCoefficients θ) x hx).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)).const_smul (Real.sqrt (((n+2 : ℕ) : ℝ)/(d : ℝ)))
  have hLaw := latitude_posterior_transverse_residualLaw hd μ hQ w hw e he hq y hy l hl x hx target
  have hp := observable_map_eq _ _ X Y hX hY hLaw
    (fun f => ContinuousFieldPartition.logPartition ν β f/((n+2 : ℕ) : ℝ))
    ((ContinuousFieldPartition.logPartition_measurable ν β).div_const _)
  simpa only [Function.comp_def,X,Y,compact_logPartition_smul] using hp

end
end SlowEquilibration.SphericalTaylorRemainder
