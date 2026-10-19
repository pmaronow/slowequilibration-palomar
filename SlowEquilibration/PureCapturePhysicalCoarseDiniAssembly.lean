-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalCoarseDiniGeometry
public import SlowEquilibration.PureCapturePhysicalCoarseDiniLowEnergy
public import SlowEquilibration.PureCapturePhysicalAsymptoticFullCompletion
public import SlowEquilibration.PureCapturePhysicalDSFiniteBridge

/-! Source Proposition 9.16, reduced to its three physical inputs.
The finite score compactness and Dini argument are already proved for actual
physical overlap laws. Here the replica count is chosen before the overlap
tolerance, the ordinary replicated-mean energy estimate controls every finite
query ensemble, and high-energy relocation transfers the resulting query cap
to an actual original-field critical point. -/

@[expose] public section
namespace SlowEquilibration.PureCapturePhysicalCoarseDiniAssembly
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalForm
open SphericalGaussianJet SphericalAging.HardSphereDynamics
open PureCapturePhysicalCoarseTransfer PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalCoarseLimit PureCapturePhysicalDiagonalBridge
open PureCapturePhysicalAsymptoticFullLift PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullToScore PureCaptureRandomDirectingScoreArray
open PureCapturePhysicalReplicaExclusionDirecting PureCapturePhysicalDSFiniteBridge
open PureCapturePhysicalAsymptoticFullCompletion
open PureCapturePhysicalCoarseDiniGeometry PureCapturePhysicalCoarseDiniLowEnergy
open OverlapPaper
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The physical directing-norm input is imposed on actual full-overlap
tail limits and their genuine full Dovbysh--Sudakov representations. -/
def PhysicalDirectingNormQ (μ : FiniteMixture) (β Q : ℝ) : Prop :=
  ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
    ∀ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
      (∀ m, z m = directingDataFullLaw R m) →
      (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) →
      ∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖^2=Q

/-- The source replicated-mean estimate concerns ordinary Gibbs replicas,
before selecting a query or a successful companion block. -/
def PhysicalReplicaMeanEnergy (μ : FiniteMixture) (β Q e : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ k₀ : ℕ, ∃ η : ℝ, 0 < η ∧
    ∀ k : ℕ, k₀ ≤ k → Tendsto
      (fun n => expectedReplicaMeanLowEnergy (k := k) n μ β Q η e τ)
      atTop (𝓝 (0:ℝ))

/-- Uniform relocation of every sufficiently high-energy physical center
on one measurable original-disorder event of probability tending to one. -/
def PhysicalHighEnergyRelocation (μ : FiniteMixture) (e : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ τ₀ : ℝ, 0 < τ₀ ∧
    ∃ Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree),
      (∀ n, MeasurableSet (Ω n)) ∧
      (∀ n, ∀ J ∈ Ω n, ∀ w : Vector (n+2),
        ‖w‖^2=(n+2:ℕ) →
        (n+2:ℕ)*(e-τ₀) ≤ field (mixtureCoefficients μ) J w →
        ∃ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) ∧
          surfaceGradient (field (mixtureCoefficients μ) J) u=0 ∧
          ‖u-w‖ ≤ r*Real.sqrt (n+2:ℕ) ∧
          field (mixtureCoefficients μ) J w ≤
            field (mixtureCoefficients μ) J u) ∧
      Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ)
        atTop (𝓝 (0:ℝ))

/-- Unconditional DS existence discharges the representation part of the
norm-Q score input; the sole remaining assumption here is the physical norm. -/
theorem normQ_score_representation_of_physical_norm
    (μ : FiniteMixture) (β Q : ℝ) (hNorm : PhysicalDirectingNormQ μ β Q)
    (k : ℕ) :
    ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖^2=Q) ∧
        ∀ T, fullToScoreArray k z T=R.scoreLaw k T := by
  intro z hz
  obtain ⟨R,hrep,hball⟩ := physicalFullAsymptoticLimit_randomDirecting μ β hz
  exact ⟨R,hNorm z hz R hrep hball,
    fullToScoreArray_eq_of_directing_full_representation R k z hrep⟩

/-- Assembly using the source norm-Q conclusion in its already transported
score form. No dimension-uniform finite-score estimate is assumed. -/
theorem physical_coarse_cover_of_normQ_score_mean_relocation
    (μ : FiniteMixture) (β : ℝ) {Q e a : ℝ}
    (hQ : Q ∈ Ioo (0:ℝ) 1) (ha : a < Real.sqrt Q)
    (hNorm : ∀ k : ℕ, ∀ z ∈ physicalFullAsymptoticLimitSet μ β,
      ∃ R : RandomDirectingData (ProbabilityMeasure DSHilbert) DSHilbert,
        (∀ᵐ ω ∂(R.disorderLaw), ∀ᵐ v ∂(R.directingKernel ω), ‖v‖^2=Q) ∧
        ∀ T, fullToScoreArray k z T=R.scoreLaw k T)
    (hMean : PhysicalReplicaMeanEnergy μ β Q e)
    (hRelocate : PhysicalHighEnergyRelocation μ e) :
    ∀ τ : ℝ, 0 < τ → Tendsto
      (fun n => expectedUncoveredGibbsMass n μ β a e τ) atTop (𝓝 (0:ℝ)) := by
  intro τ hτ
  let a₁ := (a+Real.sqrt Q)/2
  let r := (a₁-a)/2
  have ha₁ : a₁ < Real.sqrt Q := by dsimp only [a₁]; linarith
  have hr : 0 < r := by dsimp only [r,a₁]; linarith
  have hcap : a < a₁-r := by dsimp only [r,a₁]; linarith
  obtain ⟨τ₀,hτ₀,Ω,hΩ,hrelocate,hrelocateProb⟩ := hRelocate r hr
  let τ₁ := min τ τ₀
  have hτ₁ : 0 < τ₁ := lt_min hτ hτ₀
  obtain ⟨k₀,η,hη,hmean⟩ := hMean τ₁ hτ₁
  obtain ⟨k,hk₀,hk,θ₀,hθ₀,hθ₀Q,hgeometry⟩ :=
    exists_replica_count_and_dimension_uniform_tolerance hQ ha₁ k₀
  let θ := min θ₀ η
  have hθ : 0 < θ := lt_min hθ₀ hη
  have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
  have hθη : θ ≤ η := min_le_right _ _
  have hscore : ∀ n : ℕ, ∀ x : Vector (n+2),
      ∀ σ : Fin k → Vector (n+2), OnSphere x → (∀ i, OnSphere (σ i)) →
      goodCompanionBlock Q θ x σ →
      ‖physicalTrainingCenter σ‖^2=(n+2:ℕ) ∧
        a₁ < overlap x (physicalTrainingCenter σ) := by
    intro n x σ hx hσ hgood
    apply hgeometry (n+2) (by omega) x σ hx hσ
    exact ⟨fun i j hij => (hgood.1 i j hij).trans_le hθθ₀,
      fun i => (hgood.2 i).trans_le hθθ₀⟩
  have hrelocate' : ∀ n, ∀ J ∈ Ω n, ∀ w : Vector (n+2),
      ‖w‖^2=(n+2:ℕ) →
      (n+2:ℕ)*(e-τ₁) ≤ field (mixtureCoefficients μ) J w →
      ∃ u : Vector (n+2), ‖u‖^2=(n+2:ℕ) ∧
        surfaceGradient (field (mixtureCoefficients μ) J) u=0 ∧
        ‖u-w‖ ≤ r*Real.sqrt (n+2:ℕ) ∧
        field (mixtureCoefficients μ) J w ≤
          field (mixtureCoefficients μ) J u := by
    intro n J hJ w hw henergy
    apply hrelocate n J hJ w hw
    exact (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (min_le_right τ τ₀) e) (Nat.cast_nonneg _)).trans henergy
  exact expectedUncoveredGibbsMass_tendsto_zero_of_asymptotic_full_array_source_inputs
    μ β hθ (min_le_left τ τ₀) hcap hscore Ω hΩ hrelocate' hrelocateProb
    (hNorm k) (fun T => expectedFiniteLowEnergy_tendsto_zero_of_replica_mean
      μ β Q θ η e τ₁ hθη (hmean k hk₀) T)

/-- Source coarse-cover conclusion on the real original-disorder Gibbs
expectation, from precisely norm-Q, replicated-mean energy and relocation. -/
theorem physical_coarse_cover_of_three_physical_inputs
    (μ : FiniteMixture) (β : ℝ) {Q e a : ℝ}
    (hQ : Q ∈ Ioo (0:ℝ) 1) (ha : a < Real.sqrt Q)
    (hNorm : PhysicalDirectingNormQ μ β Q)
    (hMean : PhysicalReplicaMeanEnergy μ β Q e)
    (hRelocate : PhysicalHighEnergyRelocation μ e) :
    ∀ τ : ℝ, 0 < τ → Tendsto
      (fun n => expectedUncoveredGibbsMass n μ β a e τ) atTop (𝓝 (0:ℝ)) := by
  exact physical_coarse_cover_of_normQ_score_mean_relocation μ β hQ ha
    (normQ_score_representation_of_physical_norm μ β Q hNorm) hMean hRelocate

end
end SlowEquilibration.PureCapturePhysicalCoarseDiniAssembly
