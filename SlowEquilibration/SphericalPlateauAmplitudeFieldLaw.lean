-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudePhysicalCovariance
public import SlowEquilibration.SphericalLatitudeFrameParseval
public import SlowEquilibration.SphericalTaylorResidualLaw

@[expose] public section

/-! # Literal whole-field law of the source amplitude bank at amplitude one -/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel WholeFieldRegression SphericalTaylorRemainder GaussianContinuousFieldLaw SphericalGaussianJet
open scoped BigOperators Topology InnerProductSpace
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev BankCoordinate (n : ℕ) (μ : FiniteMixture) :=
  (i : BankIndex μ) × SphericalAging.FiniteModel.TensorIndex n i.2.val
abbrev EuclideanBank (n : ℕ) (μ : FiniteMixture) := EuclideanSpace ℝ (BankCoordinate n μ)

def flatBank {n : ℕ} {μ : FiniteMixture} (D : BankDisorder n μ) : BankCoordinate n μ → ℝ :=
  fun i => D i.1 i.2

def euclideanBank {n : ℕ} {μ : FiniteMixture} (D : BankDisorder n μ) : EuclideanBank n μ :=
  WithLp.toLp 2 (flatBank D)

def unpackBankCLM (n : ℕ) (μ : FiniteMixture) : EuclideanBank n μ →L[ℝ] BankDisorder n μ :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun I => EuclideanSpace.proj ⟨i,I⟩))

@[simp] theorem unpackBank_euclideanBank {n : ℕ} {μ : FiniteMixture} (D : BankDisorder n μ) :
    unpackBankCLM n μ (euclideanBank D)=D := rfl

theorem flatBank_measurable (n : ℕ) (μ : FiniteMixture) :
    Measurable (flatBank (n := n) (μ := μ)) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i.2).comp (measurable_pi_apply i.1)

theorem flatBank_hasLaw (n : ℕ) (μ : FiniteMixture) :
    HasLaw (flatBank (n := n) (μ := μ))
      (Measure.pi (fun _ : BankCoordinate n μ => gaussianReal 0 1)) (bankLaw n μ) := by
  refine ⟨(flatBank_measurable n μ).aemeasurable,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (flatBank_measurable n μ) (MeasurableSet.pi Set.countable_univ (fun i _ => hs i))]
  have hpre : flatBank (n := n) (μ := μ) ⁻¹' Set.pi univ s=
      Set.pi univ (fun i : BankIndex μ => Set.pi univ (fun I => s ⟨i,I⟩)) := by
    ext D
    simp only [mem_preimage,mem_pi,mem_univ,true_implies,flatBank]
    change (∀ i : BankCoordinate n μ,D i.1 i.2 ∈ s i) ↔
      ∀ i : BankIndex μ,∀ I,D i I ∈ s ⟨i,I⟩
    constructor
    · exact fun h i I => h ⟨i,I⟩
    · exact fun h i => h i.1 i.2
  rw [hpre,bankLaw,Measure.pi_pi]
  simp only [SphericalAging.FiniteModel.disorderLaw,Measure.pi_pi]
  exact (Fintype.prod_sigma (fun i : BankCoordinate n μ => (gaussianReal 0 1) (s i))).symm

theorem euclideanBank_measurable (n : ℕ) (μ : FiniteMixture) :
    Measurable (euclideanBank (n := n) (μ := μ)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : BankCoordinate n μ => ℝ)).symm.continuous.measurable.comp
    (flatBank_measurable n μ)

theorem actual_bank_flattened_gaussian (n : ℕ) (μ : FiniteMixture) :
    HasLaw (euclideanBank (n := n) (μ := μ)) (stdGaussian (EuclideanBank n μ)) (bankLaw n μ) := by
  have hm : Measurable (WithLp.toLp 2 : (BankCoordinate n μ → ℝ) → EuclideanBank n μ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : BankCoordinate n μ => ℝ)).symm.continuous.measurable
  change HasLaw (fun D : BankDisorder n μ => WithLp.toLp 2 (flatBank D)) _ _
  simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using
    (hasLaw_map hm.aemeasurable).fun_comp (flatBank_hasLaw n μ)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def bankContinuousField {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : K → Vector (n+1)) (hu : Continuous u) : EuclideanBank n μ →L[ℝ] C(K,ℝ) :=
  featureContinuousField (fun z => (amplitudeFieldCLM μ x e p₀ s (u z)).comp (unpackBankCLM n μ))
    (fun D => by
      simp only [ContinuousLinearMap.comp_apply,amplitudeFieldCLM_apply]
      exact (amplitudeField_contDiff μ x e p₀ s (unpackBankCLM n μ D)).continuous.comp hu)

omit [CompactSpace K] in
@[simp] theorem bankContinuousField_apply {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : K → Vector (n+1)) (hu : Continuous u) (D : EuclideanBank n μ) (z : K) :
    bankContinuousField μ x e p₀ s u hu D z=amplitudeField μ x e p₀ s (unpackBankCLM n μ D) (u z) :=
  amplitudeFieldCLM_apply μ x e p₀ s (u z) (unpackBankCLM n μ D)

/-- Genuine equality of the entire continuous random polynomial restricted
to any compact parameter set, with the original physical tensor disorder.
This identifies the bank at amplitude one, not just separate marginals. -/
theorem bankContinuousField_law_one {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (hx : ‖x‖^2=(n+1:ℝ)) (p₀ : Degree μ.maxDegree)
    (u : K → Vector (n+1)) (hu : Continuous u)
    [SecondCountableTopology K] [T2Space K] [Nonempty K] :
    (bankLaw n μ).map (fun D => bankContinuousField μ x (latitudeFrameAt x) p₀ (fun _ => 1) u hu
      (euclideanBank D))=
    (disorderLaw (n+1) μ.maxDegree).map (fun D =>
      modelContinuousField (mixtureCoefficients μ) u hu (euclideanDisorder D)) := by
  let X := bankContinuousField μ x (latitudeFrameAt x) p₀ (fun _ => 1) u hu
  let Y := modelContinuousField (mixtureCoefficients μ) u hu
  have hcov : ∀ a b : K,cov[fun D => X D a,fun D => X D b;stdGaussian (EuclideanBank n μ)]=
      cov[fun D => Y D a,fun D => Y D b;stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)] := by
    intro a b
    have hX := (actual_bank_flattened_gaussian n μ).covariance_fun_comp
      (f := fun D => X D a) (g := fun D => X D b) (by fun_prop) (by fun_prop)
    have hY := (actual_flattened_gaussian (n+1) μ.maxDegree).covariance_fun_comp
      (f := fun D => Y D a) (g := fun D => Y D b) (by fun_prop) (by fun_prop)
    have hcX : cov[fun D : BankDisorder n μ => X (euclideanBank D) a,
        fun D => X (euclideanBank D) b;bankLaw n μ]=(n+1:ℝ)*μ.xi (overlap (u a) (u b)) := by
      simp only [X,bankContinuousField_apply,unpackBank_euclideanBank]
      exact amplitudeField_covariance_one_of_parseval μ x (latitudeFrameAt x)
        (fun u v => by simpa only [Nat.cast_add,Nat.cast_one] using
          latitudeFrameAt_adjoint_inner x (by simpa only [Nat.cast_add,Nat.cast_one] using hx) u v) p₀ (u a) (u b)
    have hcY : cov[fun D : Disorder (n+1) μ.maxDegree => Y (euclideanDisorder D) a,
        fun D => Y (euclideanDisorder D) b;disorderLaw (n+1) μ.maxDegree]=
        (n+1:ℝ)*μ.xi (overlap (u a) (u b)) := by
      simp only [Y,modelContinuousField_apply,valueObservation,flatJetCLM_apply,jet,iteratedFDeriv_zero_apply,unpack_euclideanDisorder]
      simpa only [covariancePolynomial_mixture,Nat.cast_add,Nat.cast_one] using
        field_covariance (by omega : 0<n+1) (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) (u a) (u b)
    exact hX.symm.trans (hcX.trans (hcY.symm.trans hY))
  have hLaw := continuous_field_law_eq_of_covariance X Y hcov
  have hLeft := congrArg (fun ν => ν.map X) (actual_bank_flattened_gaussian n μ).map_eq
  have hRight := congrArg (fun ν => ν.map Y) (actual_flattened_gaussian (n+1) μ.maxDegree).map_eq
  rw [Measure.map_map X.continuous.measurable (euclideanBank_measurable n μ)] at hLeft
  rw [Measure.map_map Y.continuous.measurable (euclideanDisorder_measurable _ _)] at hRight
  exact hLeft.trans (hLaw.trans hRight.symm)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
