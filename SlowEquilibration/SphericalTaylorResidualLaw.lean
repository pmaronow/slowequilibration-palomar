-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorContinuousLaw
public import SlowEquilibration.SphericalTaylorResidualKernel

@[expose] public section

/-! The literal transverse Taylor remainder has the entire continuous-field
law of the actual finite residual mixture, with its physical sqrt(N/d) factor. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.GaussianContinuousFieldLaw
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def modelContinuousField {d P : ℕ} (c : Degree P → ℝ) (x : K → Vector d)
    (hx : Continuous x) : EuclideanDisorder d P →L[ℝ] C(K,ℝ) :=
  featureContinuousField (fun u => valueObservation c (x u)) (fun g => by
    simp only [valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply]
    exact (field_contDiff c (unpackDisorder g)).continuous.comp hx)

omit [CompactSpace K] in
@[simp] theorem modelContinuousField_apply {d P : ℕ} (c : Degree P → ℝ) (x : K → Vector d)
    (hx : Continuous x) (g : EuclideanDisorder d P) (u : K) :
    modelContinuousField c x hx g u=valueObservation c (x u) g := rfl

theorem scalar_coupling_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f g : E →L[ℝ] ℝ) (s : ℝ) :
    (s • f) ((s • g).adjoint 1)=s^2*f (g.adjoint 1) := by
  have hs : (s • g).adjoint=s • g.adjoint := by
    simp
  rw [hs]
  simp only [smul_apply,map_smul,smul_eq_mul]
  ring

omit [CompactSpace K] in
theorem transverseOffset_parameter_continuous {N d : ℕ}
    (e : Vector d →ₗᵢ[ℝ] Vector N) (q : ℝ) (x : K → Vector d) (hx : Continuous x) :
    Continuous (fun u => transverseOffset e q (x u)) := by
  unfold transverseOffset
  exact (e.continuous.comp hx).const_smul (Real.sqrt ((N : ℝ)*(1-q)/(q*(d : ℝ))))

/-- Literal unconditional law equality, including the actual finite residual
coefficient model and all ambient/section dimension factors. -/
theorem transverse_taylorContinuousField_law {N d : ℕ} (hN : 0<N) (hd : 0<d)
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    (μ : FiniteMixture) {q : ℝ} (hq : q∈Set.Ioo (0 : ℝ) 1)
    (m : Vector N) (hm : ‖m‖^2=(N : ℝ)) (e : Vector d →ₗᵢ[ℝ] Vector N)
    (he : ∀ y,inner ℝ (e y) m=0) (x : K → Vector d) (hx : Continuous x) :
    let c := centerCoefficients (mixtureCoefficients μ) q
    let θ := μ.taylorResidual hq.1 (sub_pos.mpr hq.2)
    let z := fun u => transverseOffset e q (x u)
    let hz : Continuous z := transverseOffset_parameter_continuous e q x hx
    (disorderLaw N μ.maxDegree).map
      (fun J => taylorContinuousField c m z hz (euclideanDisorder J))=
    (disorderLaw d θ.maxDegree).map
      (fun J => Real.sqrt ((N : ℝ)/(d : ℝ)) • modelContinuousField (mixtureCoefficients θ) x hx (euclideanDisorder J)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) q
  let θ := μ.taylorResidual hq.1 (sub_pos.mpr hq.2)
  let z := fun u => transverseOffset e q (x u)
  have hz : Continuous z := transverseOffset_parameter_continuous e q x hx
  let X := taylorContinuousField c m z hz
  let Y := Real.sqrt ((N : ℝ)/(d : ℝ)) • modelContinuousField (mixtureCoefficients θ) x hx
  have hgram : ∀ u v : K,evaluationFeature X u ((evaluationFeature X v).adjoint 1)=
      evaluationFeature Y u ((evaluationFeature Y v).adjoint 1) := by
    intro u v
    have hX (u : K) : evaluationFeature X u=taylorRemainderCLM c m (z u) := rfl
    have hY (u : K) : evaluationFeature Y u=
        Real.sqrt ((N : ℝ)/(d : ℝ)) • valueObservation (mixtureCoefficients θ) (x u) := by
      ext g
      rfl
    rw [hX u,hX v,hY u,hY v,scalar_coupling_smul,
      value_value_coupling hd _ (mixtureCoefficients_nonnegative θ),
      covariancePolynomial_mixture,Real.sq_sqrt (by positivity)]
    rw [transverse_taylorRemainder_kernel hN hd μ hq m hm e he]
    have hd0 : (d : ℝ)≠0 := Nat.cast_ne_zero.mpr hd.ne'
    field_simp [hd0]
    rfl
  have hLaw : (stdGaussian (EuclideanDisorder N μ.maxDegree)).map X=
      (stdGaussian (EuclideanDisorder d θ.maxDegree)).map Y := by
    apply continuous_field_law_eq X Y
    intro u v
    rw [evaluation_feature_inner,evaluation_feature_inner]
    exact hgram u v
  have hleft := congrArg (fun ν => ν.map X) (actual_flattened_gaussian N μ.maxDegree).map_eq
  have hright := congrArg (fun ν => ν.map Y) (actual_flattened_gaussian d θ.maxDegree).map_eq
  rw [Measure.map_map X.continuous.measurable (euclideanDisorder_measurable _ _)] at hleft
  rw [Measure.map_map Y.continuous.measurable (euclideanDisorder_measurable _ _)] at hright
  exact hleft.trans (hLaw.trans hright.symm)

end
end SlowEquilibration.SphericalTaylorRemainder
