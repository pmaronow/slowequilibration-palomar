-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeModel

@[expose] public section

/-! # Actual Gaussian bank amplitude directions

Each source transverse probe is a genuine continuous-linear selection of
the Gaussian tensor bank. Varying one amplitude follows the exact affine
coefficient line D+τ probe(D), and the physical field and partition retain
their literal planted drift and source penalty.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalBarycenter
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {μ : FiniteMixture} {n : ℕ}

/-- The selected source amplitude equals 1+τ; its other amplitude remains one. -/
def amplitudeAt (k : Fin 2) (τ : ℝ) (j : Fin 2) : ℝ := if j=k then 1+τ else 1

@[simp] theorem amplitudeAt_zero (k : Fin 2) : amplitudeAt k 0=(fun _ => 1) := by
  funext j
  simp [amplitudeAt]

/-- The actual selected original-degree transverse bank block, including
all its Gaussian tensor coordinates. -/
def selectedProbeDisorder (p₀ : Degree μ.maxDegree) (k : Fin 2)
    (D : BankDisorder n μ) : BankDisorder n μ :=
  fun i => if i.1=p₀ ∧ i.2.val=k.val+1 then D i else 0

/-- Literal coefficient rescaling of every block of the actual bank. -/
def amplitudeDisorder (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) : BankDisorder n μ := fun i => bankAmplitude p₀ s i • D i

@[simp] theorem amplitudeDisorder_one (p₀ : Degree μ.maxDegree) (D : BankDisorder n μ) :
    amplitudeDisorder p₀ (fun _ => 1) D=D := by
  funext i
  simp [amplitudeDisorder,bankAmplitude_one]

theorem selectedProbeDisorder_idempotent (p₀ : Degree μ.maxDegree) (k : Fin 2)
    (D : BankDisorder n μ) :
    selectedProbeDisorder p₀ k (selectedProbeDisorder p₀ k D)=selectedProbeDisorder p₀ k D := by
  funext i
  unfold selectedProbeDisorder
  split_ifs <;> rfl

def selectedProbeCLM (n : ℕ) (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) (k : Fin 2) :
    BankDisorder n μ →L[ℝ] BankDisorder n μ :=
  ContinuousLinearMap.pi (fun i => if i.1=p₀ ∧ i.2.val=k.val+1 then
    ContinuousLinearMap.proj i else 0)

def amplitudeDisorderCLM (n : ℕ) (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    BankDisorder n μ →L[ℝ] BankDisorder n μ :=
  ContinuousLinearMap.pi (fun i => bankAmplitude p₀ s i • ContinuousLinearMap.proj i)

@[simp] theorem selectedProbeCLM_apply (p₀ : Degree μ.maxDegree) (k : Fin 2) (D : BankDisorder n μ) :
    selectedProbeCLM n μ p₀ k D=selectedProbeDisorder p₀ k D := by
  funext i
  simp only [selectedProbeCLM,selectedProbeDisorder,ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

@[simp] theorem amplitudeDisorderCLM_apply (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) : amplitudeDisorderCLM n μ p₀ s D=amplitudeDisorder p₀ s D := by
  funext i
  rfl

theorem bankAmplitude_at (p₀ : Degree μ.maxDegree) (k : Fin 2) (τ : ℝ) (i : BankIndex μ) :
    bankAmplitude p₀ (amplitudeAt k τ) i=
      if i.1=p₀ ∧ i.2.val=k.val+1 then 1+τ else 1 := by
  fin_cases k <;> simp only [bankAmplitude,amplitudeAt]
  all_goals split_ifs <;> simp_all

/-- The source amplitude is exactly an affine line in actual Gaussian
bank coordinates, including every unselected block. -/
theorem amplitudeDisorder_at (p₀ : Degree μ.maxDegree) (k : Fin 2) (τ : ℝ)
    (D : BankDisorder n μ) :
    amplitudeDisorder p₀ (amplitudeAt k τ) D=D+τ • selectedProbeDisorder p₀ k D := by
  funext i
  change bankAmplitude p₀ (amplitudeAt k τ) i • D i=
    D i+τ • selectedProbeDisorder p₀ k D i
  rw [bankAmplitude_at]
  unfold selectedProbeDisorder
  split_ifs <;> simp [add_smul]

theorem amplitudeDisorderCLM_at (p₀ : Degree μ.maxDegree) (k : Fin 2) (τ : ℝ) :
    amplitudeDisorderCLM n μ p₀ (amplitudeAt k τ)=
      ContinuousLinearMap.id ℝ (BankDisorder n μ)+τ • selectedProbeCLM n μ p₀ k := by
  apply ContinuousLinearMap.ext
  intro D
  simp only [amplitudeDisorderCLM_apply,add_apply,
    smul_apply,ContinuousLinearMap.id_apply,selectedProbeCLM_apply]
  exact amplitudeDisorder_at p₀ k τ D

/-- Rescaling the actual bank has exactly the same effect as the physical
field amplitude, with no equality-in-law replacement. -/
theorem amplitudeField_eq_rescaled_disorder (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) (u : Vector (n+1)) :
    amplitudeField μ x e p₀ s D u=
      amplitudeField μ x e p₀ (fun _ => 1) (amplitudeDisorder p₀ s D) u := by
  unfold amplitudeField
  apply Finset.sum_congr rfl
  intro i _
  rw [bankAmplitude_one,one_mul]
  change bankAmplitude p₀ s i*bankComponent μ x e i (D i) u=
    bankComponent μ x e i (bankAmplitude p₀ s i • D i) u
  have h := (bankComponentCLM μ x e i u).map_smul (bankAmplitude p₀ s i) (D i)
  simpa only [bankComponentCLM_apply,smul_eq_mul] using h.symm

/-- The actual field along one source probe is affine pointwise on the
entire ambient space. -/
theorem amplitudeField_at_affine (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (k : Fin 2) (τ : ℝ)
    (D : BankDisorder n μ) (u : Vector (n+1)) :
    amplitudeField μ x e p₀ (amplitudeAt k τ) D u=
      amplitudeField μ x e p₀ (fun _ => 1) D u+
        τ*amplitudeField μ x e p₀ (fun _ => 1) (selectedProbeDisorder p₀ k D) u := by
  rw [amplitudeField_eq_rescaled_disorder,amplitudeDisorder_at]
  have h := (amplitudeFieldCLM μ x e p₀ (fun _ => 1) u).map_add D (τ • selectedProbeDisorder p₀ k D)
  rw [map_smul] at h
  simpa only [amplitudeFieldCLM_apply,smul_eq_mul] using h

theorem amplitudePlantedField_at_affine (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (k : Fin 2) (τ : ℝ)
    (D : BankDisorder n μ) (u : Vector (n+1)) :
    amplitudePlantedField μ β x e p₀ (amplitudeAt k τ) D u=
      amplitudePlantedField μ β x e p₀ (fun _ => 1) D u+
        τ*amplitudeField μ x e p₀ (fun _ => 1) (selectedProbeDisorder p₀ k D) u := by
  unfold amplitudePlantedField
  rw [amplitudeField_at_affine]
  ring

theorem amplitudePartition_at_line (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (k : Fin 2) (τ : ℝ)
    (D : BankDisorder n μ) :
    amplitudePartition μ β J δ q₁ q₂ x e p₀ (amplitudeAt k τ) D=
      ∫ u, Real.exp (β*(amplitudePlantedField μ β x e p₀ (fun _ => 1) D u+
        τ*amplitudeField μ x e p₀ (fun _ => 1) (selectedProbeDisorder p₀ k D) u)-
          2*(n+1 : ℝ)*sourceProfile J δ q₁ q₂ (overlap x u)) ∂sphereLaw (n+1) := by
  unfold amplitudePartition
  apply integral_congr_ae
  exact .of_forall fun u => by
    dsimp only
    rw [amplitudePlantedField_at_affine]

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
