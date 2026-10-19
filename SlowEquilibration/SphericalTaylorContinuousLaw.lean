-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorRemainderConditioning
public import SlowEquilibration.SphericalLatitudeCountIntegral
public import SlowEquilibration.GaussianContinuousFieldCovariance

@[expose] public section

/-! Literal continuous Taylor-remainder fields keep their complete Borel law
under every affine first-jet posterior target. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.SphericalLatitudeChartKacRice
open SlowEquilibration.ContinuousFieldLaw
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual finite-coefficient continuous field, as one continuous linear
map into the uniform-norm space of continuous sample functions. -/
def featureContinuousField (L : K → E →L[ℝ] ℝ)
    (hL : ∀ g,Continuous (fun x => L x g)) : E →L[ℝ] C(K,ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => ⟨fun x => L x g,hL g⟩
      map_add' := by intro g h; ext x; exact map_add (L x) g h
      map_smul' := by intro a g; ext x; exact map_smul (L x) a g }

omit [CompactSpace K] in
@[simp] theorem featureContinuousField_apply (L : K → E →L[ℝ] ℝ)
    (hL : ∀ g,Continuous (fun x => L x g)) (g : E) (x : K) :
    featureContinuousField L hL g x=L x g := rfl

omit [CompactSpace K] in
theorem taylorRemainder_parameter_continuous {N P : ℕ} (c : Degree P → ℝ) (m : Vector N)
    (z : K → Vector N) (hz : Continuous z) (g : EuclideanDisorder N P) :
    Continuous (fun x => taylorRemainderCLM c m (z x) g) := by
  simp only [taylorRemainderCLM,valueObservation,directionObservation,sub_apply,flatJetCLM_apply,
    jet,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply]
  exact ((field_contDiff c (unpackDisorder g)).continuous.comp (continuous_const.add hz)).sub
    continuous_const |>.sub ((fderiv ℝ (field c (unpackDisorder g)) m).continuous.comp hz)

def taylorContinuousField {N P : ℕ} (c : Degree P → ℝ) (m : Vector N)
    (z : K → Vector N) (hz : Continuous z) : EuclideanDisorder N P →L[ℝ] C(K,ℝ) :=
  featureContinuousField (fun x => taylorRemainderCLM c m (z x))
    (taylorRemainder_parameter_continuous c m z hz)

omit [CompactSpace K] in
@[simp] theorem taylorContinuousField_apply {N P : ℕ} (c : Degree P → ℝ) (m : Vector N)
    (z : K → Vector N) (hz : Continuous z) (g : EuclideanDisorder N P) (x : K) :
    taylorContinuousField c m z hz g x=taylorRemainderCLM c m (z x) g := rfl

theorem euclideanDisorder_measurable (N P : ℕ) : Measurable (euclideanDisorder (N := N) (P := P)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
    (flatDisorder_measurable N P)

/-- Exact equality of whole continuous-field laws, at every posterior
value/radial/gradient target; no pressure or finite-law hypothesis remains. -/
theorem latitude_posterior_taylorContinuousField_map
    [SecondCountableTopology K] [T2Space K] [Nonempty K]
    {n P : ℕ} (c : Degree P → ℝ) (hc : ∀ p,0≤c p) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (z : K → Vector (n+2)) (hz : Continuous z)
    (ht : ∀ x,inner ℝ (z x) (latitudeMap w e q y)=0)
    (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    (coefficientKernel (latitudeJointCLM c w e q y hy) target).map
      (fun J => taylorContinuousField c (latitudeMap w e q y) z hz (euclideanDisorder J))=
    (disorderLaw (n+2) P).map
      (fun J => taylorContinuousField c (latitudeMap w e q y) z hz (euclideanDisorder J)) := by
  let X := fun J : Disorder (n+2) P =>
    taylorContinuousField c (latitudeMap w e q y) z hz (euclideanDisorder J)
  have hX : Measurable X := (taylorContinuousField c (latitudeMap w e q y) z hz).continuous.measurable.comp
    (euclideanDisorder_measurable _ _)
  apply continuous_map_law_eq_of_finite_laws _ _ X X hX hX
  intro I
  let zi : I → Vector (n+2) := fun i => z (TopologicalSpace.denseSeq K (i : ℕ))
  have hh := latitude_posterior_taylorRemainder_family_map c hc w e q y hy zi
    (fun i => ht _) target
  let ev := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ))
  have hm : Measurable ev := ev.continuous.measurable
  have hf : Measurable (actualObservation (taylorRemainderFamily c (latitudeMap w e q y) zi)) :=
    (taylorRemainderFamily c (latitudeMap w e q y) zi).continuous.measurable.comp
      (euclideanDisorder_measurable _ _)
  have hh' := congrArg (fun ν => ν.map ev) hh
  rw [Measure.map_map hm hf,Measure.map_map hm hf] at hh'
  exact hh'

end
end SlowEquilibration.SphericalTaylorRemainder
