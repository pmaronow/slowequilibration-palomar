-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaPlateau
public import SlowEquilibration.SphericalLatitude

@[expose] public section

/-! # Concrete Gaussian bank and source plateau amplitude partition

Every latitude degree, including zero, one, and two, has an actual ordered
standard Gaussian tensor. The model changes the two selected transverse
amplitudes and retains a literal sphere Gibbs law. Equality in law with the
original ambient field and the perturbed pressure limit are separate proof
obligations; they are not asserted by this module.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter
open scoped BigOperators Topology InnerProductSpace
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {μ : FiniteMixture}

/-- All finitely many latitude degrees, with the original physical degree
retained. In particular a mixture without degree two still has bank degree two. -/
abbrev BankIndex (μ : FiniteMixture) := (p : Degree μ.maxDegree) × Fin (p.val.val+1)

abbrev BankDisorder (n : ℕ) (μ : FiniteMixture) :=
  (i : BankIndex μ) → SphericalAging.FiniteModel.Disorder n i.2.val

def bankLaw (n : ℕ) (μ : FiniteMixture) : Measure (BankDisorder n μ) :=
  Measure.pi (fun i : BankIndex μ => SphericalAging.FiniteModel.disorderLaw n i.2.val)

instance bankLaw_probability (n : ℕ) (μ : FiniteMixture) :
    IsProbabilityMeasure (bankLaw n μ) := by
  unfold bankLaw
  infer_instance

theorem bank_independent (n : ℕ) (μ : FiniteMixture) :
    iIndepFun (fun i (D : BankDisorder n μ) => D i) (bankLaw n μ) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem bankBlock_hasLaw (n : ℕ) (μ : FiniteMixture) (i : BankIndex μ) :
    HasLaw (fun D : BankDisorder n μ => D i)
      (SphericalAging.FiniteModel.disorderLaw n i.2.val) (bankLaw n μ) :=
  (measurePreserving_eval (fun i : BankIndex μ =>
    SphericalAging.FiniteModel.disorderLaw n i.2.val) i).hasLaw

theorem bank_hasGaussianLaw (n : ℕ) (μ : FiniteMixture) :
    HasGaussianLaw (id : BankDisorder n μ → BankDisorder n μ) (bankLaw n μ) := by
  apply (bank_independent n μ).hasGaussianLaw
  intro i
  have : IsGaussian (SphericalAging.FiniteModel.disorderLaw n i.2.val) := by
    have h := SphericalAging.FiniteModel.disorder_hasGaussianLaw n i.2.val
    simpa only [Measure.map_id] using h.isGaussian_map
  exact (bankBlock_hasLaw n μ i).hasGaussianLaw

/-- The source binomial coefficient. -/
def bankCoefficient (μ : FiniteMixture) (i : BankIndex μ) : ℝ :=
  Real.sqrt (mixtureCoefficients μ i.1 * (Nat.choose i.1.val.val i.2.val : ℝ))

/-- The selected original degree is perturbed only in transverse degrees one
and two. All other independent Gaussian components retain amplitude one. -/
def bankAmplitude (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (i : BankIndex μ) : ℝ :=
  if i.1=p₀ ∧ i.2.val=1 then s 0 else if i.1=p₀ ∧ i.2.val=2 then s 1 else 1

/-- The polynomial full ambient extension of a single bank component. Raw
tensor monomials ensure that degree zero has variance N, not variance one. -/
def bankComponent {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ)
    (D : SphericalAging.FiniteModel.Disorder n i.2.val) (u : Vector (n+1)) : ℝ :=
  Real.sqrt (n+1:ℝ) * bankCoefficient μ i * overlap x u^(i.1.val.val-i.2.val) *
    ((Real.sqrt (n+1:ℝ))⁻¹)^i.2.val *
    SphericalAging.FiniteModel.tensorLinear
      (SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u)) D

/-- Actual Gaussian polynomial with the literal two source amplitudes. -/
def amplitudeField {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) (u : Vector (n+1)) : ℝ :=
  ∑ i : BankIndex μ, bankAmplitude p₀ s i * bankComponent μ x e i (D i) u

/-- The genuine deterministic planted shift of this concrete Gaussian field. -/
def amplitudePlantedField {n : ℕ} (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) (u : Vector (n+1)) : ℝ :=
  amplitudeField μ x e p₀ s D u + β*(n+1:ℝ)*μ.xi (overlap x u)

/-- Literal source weighted partition, including the source smooth penalty. -/
def amplitudePartition {n : ℕ} (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) : ℝ :=
  ∫ u, Real.exp (β*amplitudePlantedField μ β x e p₀ s D u-
    2*(n+1:ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)) ∂sphereLaw (n+1)

/-- The true finite-volume source amplitude pressure. -/
def amplitudeExpectedPressure {n : ℕ} (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) : ℝ :=
  (∫ D, Real.log (amplitudePartition μ β J δ q₁ q₂ x e p₀ s D) ∂bankLaw n μ)/(n+1:ℝ)

/-- Genuine normalized Gibbs replicas at every perturbation value. -/
def amplitudeWeightedLaw {n : ℕ} (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (D : BankDisorder n μ) : Measure (Vector (n+1)) :=
  weightedLaw β (amplitudePlantedField μ β x e p₀ s D) (sourceProfile J δ q₁ q₂) x

/-- The covariance polynomial of a latitude in the actual perturbed bank. -/
def amplitudeLatitudeCovariance (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r t : ℝ) : ℝ :=
  ∑ i : BankIndex μ, bankAmplitude p₀ s i^2 * mixtureCoefficients μ i.1 *
    (Nat.choose i.1.val.val i.2.val:ℝ)*r^(2*(i.1.val.val-i.2.val))*(1-r^2)^i.2.val*t^i.2.val

lemma bankAmplitude_one (p₀ : Degree μ.maxDegree) (i : BankIndex μ) :
    bankAmplitude p₀ (fun _ => 1) i=1 := by simp [bankAmplitude]

theorem bankComponent_contDiff {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ)
    (D : SphericalAging.FiniteModel.Disorder n i.2.val) :
    ContDiff ℝ ⊤ (bankComponent μ x e i D) := by
  unfold bankComponent SphericalAging.FiniteModel.tensorLinear
  have hR : ContDiff ℝ ⊤ (fun u : Vector (n+1) => overlap x u) :=
    (contDiff_const.inner ℝ contDiff_id).div_const _
  have hT : ContDiff ℝ ⊤ (fun u : Vector (n+1) =>
      ∑ I : SphericalAging.FiniteModel.TensorIndex n i.2.val,
        SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u) I*D I) :=
    ContDiff.sum fun I _ =>
      ((SphericalAging.FiniteModel.tensorMonomial_contDiff I).comp
        e.toContinuousLinearMap.adjoint.contDiff).mul contDiff_const
  exact (((contDiff_const.mul contDiff_const).mul (hR.pow _)).mul contDiff_const).mul hT

theorem amplitudeField_contDiff {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) : ContDiff ℝ ⊤ (amplitudeField μ x e p₀ s D) := by
  unfold amplitudeField
  exact ContDiff.sum fun i _ => contDiff_const.mul (bankComponent_contDiff μ x e i (D i))

/-- Every actual bank component is linear in its genuine Gaussian tensor. -/
def bankComponentCLM {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ) (u : Vector (n+1)) :
    SphericalAging.FiniteModel.Disorder n i.2.val →L[ℝ] ℝ :=
  (Real.sqrt (n+1:ℝ)*bankCoefficient μ i*overlap x u^(i.1.val.val-i.2.val)*
    ((Real.sqrt (n+1:ℝ))⁻¹)^i.2.val) •
    ∑ I : SphericalAging.FiniteModel.TensorIndex n i.2.val,
      SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u) I •
        ContinuousLinearMap.proj I

@[simp] theorem bankComponentCLM_apply {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (i : BankIndex μ) (u : Vector (n+1))
    (D : SphericalAging.FiniteModel.Disorder n i.2.val) :
    bankComponentCLM μ x e i u D=bankComponent μ x e i D u := by
  simp [bankComponentCLM,bankComponent,SphericalAging.FiniteModel.tensorLinear]

/-- The complete perturbed polynomial is one actual continuous linear
functional of the actual independent Gaussian bank. -/
def amplitudeFieldCLM {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) : BankDisorder n μ →L[ℝ] ℝ :=
  ∑ i : BankIndex μ, bankAmplitude p₀ s i •
    (bankComponentCLM μ x e i u).comp (ContinuousLinearMap.proj i)

@[simp] theorem amplitudeFieldCLM_apply {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) (D : BankDisorder n μ) :
    amplitudeFieldCLM μ x e p₀ s u D=amplitudeField μ x e p₀ s D u := by
  simp [amplitudeFieldCLM,amplitudeField]

theorem amplitudeField_hasGaussianLaw {n : ℕ} (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) :
    HasGaussianLaw (fun D : BankDisorder n μ => amplitudeField μ x e p₀ s D u) (bankLaw n μ) := by
  simpa using (bank_hasGaussianLaw n μ).map_fun (amplitudeFieldCLM μ x e p₀ s u)

theorem amplitudeField_jointGaussian {n : ℕ} {ι : Type*} [Fintype ι]
    (μ : FiniteMixture) (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (u : ι → Vector (n+1)) :
    HasGaussianLaw (fun D : BankDisorder n μ => fun i => amplitudeField μ x e p₀ s D (u i))
      (bankLaw n μ) := by
  simpa using (bank_hasGaussianLaw n μ).map_fun
    (ContinuousLinearMap.pi (fun i => amplitudeFieldCLM μ x e p₀ s (u i)))

theorem amplitudePlantedField_contDiff {n : ℕ} (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) : ContDiff ℝ ⊤ (amplitudePlantedField μ β x e p₀ s D) := by
  have hR : ContDiff ℝ ⊤ (fun u : Vector (n+1) => overlap x u) :=
    (contDiff_const.inner ℝ contDiff_id).div_const _
  have hxi : ContDiff ℝ ⊤ μ.xi := by
    unfold FiniteMixture.xi
    exact ContDiff.sum fun p _ => contDiff_const.mul (contDiff_id.pow p)
  exact (amplitudeField_contDiff μ x e p₀ s D).add
    (contDiff_const.mul (hxi.comp hR))

theorem amplitudeWeightedLaw_probability {n : ℕ} (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    IsProbabilityMeasure (amplitudeWeightedLaw μ β J δ q₁ q₂ x e p₀ s D) :=
  weightedLaw_probability (by omega) β (amplitudePlantedField_contDiff μ β x e p₀ s D).continuous
    (sourceProfile_contDiff J δ q₁ q₂) x

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
