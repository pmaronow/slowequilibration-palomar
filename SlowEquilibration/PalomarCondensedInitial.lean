-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PalomarCondensedSourceBridge

/-! All initial-law clauses using the literal spherical Hamiltonian. The
additional standalone definitions are copied into the Mathlib-only Challenge. -/
@[expose] public section
noncomputable section
set_option backward.proofsInPublic true
namespace SlowEquilibrationCondensedSource
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory

/-- Compact physical sphere, with its inherited topology and Borel sigma algebra. -/
def fieldSphere (N : ℕ) : Set (Vector N) := Metric.sphere 0 (Real.sqrt N)

/-- Compactness of the finite-dimensional physical sphere, with its inherited Euclidean topology. -/
instance fieldSphere_compactSpace (N : ℕ) : CompactSpace (fieldSphere N) := by
  unfold fieldSphere
  infer_instance

/-- The polynomial Hamiltonian is continuous on the full ambient Euclidean space. -/
theorem field_continuous {N : ℕ} (μ : FiniteMixture) (J : Disorder N μ.maxDegree) :
    Continuous (field μ J) := by
  unfold field
  fun_prop

/-- Linear restriction of the tensor Hamiltonian to the compact physical sphere. -/
def restrictionLinear {N : ℕ} (μ : FiniteMixture) :
    Disorder N μ.maxDegree →ₗ[ℝ] C(fieldSphere N, ℝ) where
  toFun J := ⟨fun x => field μ J x.val, (field_continuous μ J).comp continuous_subtype_val⟩
  map_add' J K := by
    apply ContinuousMap.ext
    intro x
    simp only [field, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
    rfl
  map_smul' r J := by
    apply ContinuousMap.ext
    intro x
    change field μ (r • J) x.val = r * field μ J x.val
    unfold field
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc r, ← Finset.mul_sum]
    simp only [← mul_assoc, mul_comm _ r]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

/-- Continuous restriction map; continuity follows from finite-dimensional tensor space. -/
def restrictionCLM {N : ℕ} (μ : FiniteMixture) :
    Disorder N μ.maxDegree →L[ℝ] C(fieldSphere N, ℝ) :=
  LinearMap.toContinuousLinearMap (restrictionLinear μ)

/-- Actual finite-dimensional image of the spherical Hamiltonian, retaining no redundant tensors. -/
abbrev SphereField (N : ℕ) (μ : FiniteMixture) :=
  LinearMap.range (restrictionCLM (N := N) μ).toLinearMap

/-- The spherical field image is finite dimensional because its ordered tensor domain is finite dimensional. -/
instance sphereField_finiteDimensional (N : ℕ) (μ : FiniteMixture) :
    FiniteDimensional ℝ (SphereField N μ) := LinearMap.finiteDimensional_range _

/-- Projection of raw tensors onto the actual spherical function they define. -/
def sphereFieldMap {N : ℕ} (μ : FiniteMixture) :
    Disorder N μ.maxDegree →L[ℝ] SphereField N μ := (restrictionCLM μ).rangeRestrict

/-- Gaussian law of the actual spherical Hamiltonian, as an image of the tensor product law. -/
def sphereFieldLaw (N : ℕ) (μ : FiniteMixture) : Measure (SphereField N μ) :=
  (disorderLaw N μ.maxDegree).map (sphereFieldMap μ)

/-- A continuous linear right inverse of the surjective tensor-to-field map.
Choice selects coefficients representing exactly the given spherical polynomial;
the bridge proves the right-inverse identity and independence of all physical laws from this choice. -/
def sphereLift {N : ℕ} (μ : FiniteMixture) :
    SphereField N μ →L[ℝ] Disorder N μ.maxDegree :=
  Classical.choose ((sphereFieldMap μ).exists_rightInverse_of_surjective
    (restrictionCLM μ).range_rangeRestrict)

/-- Nonnegative convex weights summing to one on a finite prescribed menu. -/
abbrev MenuWeights (ι : Type*) [Fintype ι] :=
  {w : ι → ℝ // (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1}

/-- The ordinary convex combination of prescribed initial measures, with every menu weight allowed. -/
def menuMixture {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (ν : ι → Measure X) (w : MenuWeights ι) : Measure X :=
  ∑ j, ENNReal.ofReal (w.val j) • ν j

/-- Literal infimum over all convex menu weights and every time t∈[0,T].
The field argument is only the spherical Hamiltonian; its linear coefficient representative
gives the same physical diffusion for every possible representing tensor. -/
def sphereMenuDistance {N : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : FiniteMixture) (β : ℝ) (ν : ι → Measure (Vector N))
    (T : ℝ≥0) (H : SphereField N μ) : ℝ :=
  sInf {r : ℝ | ∃ w : MenuWeights ι, ∃ t : ℝ≥0, t ≤ T ∧
    r = distance μ β t (sphereLift μ H) (menuMixture ν w)}

/-- Literal all-time TV distance for a probability kernel depending on the spherical field. -/
def sphereIntervalDistance {N : ℕ} (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (SphereField N μ) (Vector N)) (H : SphereField N μ) : ℝ :=
  intervalDistance μ β T (sphereLift μ H) (κ H)

/-- Convergence in probability to c on dimension-dependent probability spaces. -/
def inProbability {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (d : ∀ N, Measure (Ω N)) (f : ∀ N, Ω N → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => (d N).real {ω | ε ≤ ‖f N ω - c‖}) atTop (𝓝 0)

/-- Extended nonnegative conditional KL is o(log N) in probability; infinite KL is included in tails. -/
def littleLogInProbability {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (d : ∀ N, Measure (Ω N)) (I : ∀ N, Ω N → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun N => (d N).real {ω | ENNReal.ofReal (ε * Real.log N) ≤ I N ω}) atTop (𝓝 0)

/-- Mutual information I(H;X₀), the KL of the actual joint law against its marginal product. -/
def fieldMutualInformation {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]
    (d : Measure D) (κ : Kernel D X) : ℝ≥0∞ :=
  InformationTheory.klDiv (d ⊗ₘ κ) (d.prod (κ ∘ₘ d))

/-- A deterministic extended nonnegative information sequence is o(log N), with eventual finiteness. -/
def littleLog (I : ℕ → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, I N ≤ ENNReal.ofReal (ε * Real.log N)

universe u v

/-- All manuscript thm:main-initial clauses and cor:cp-information, with the same γ as uniform
separation. Menus have growth κ<(d−2)/2; random menus are independent via a product law.
Adaptive initial kernels depend on the spherical Hamiltonian alone. Both KL and information
are Mathlib's extended divergences, with the precise o(log N) conditions displayed above. -/
def AllInitialConclusions (μ : FiniteMixture) (β γ : ℝ) : Prop :=
  let T := fun N => exponentialHorizon γ N
  CondensedAndInitial μ β γ ∧
  (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
      (ν : ∀ N, ι N → Measure (Vector N)) [∀ N j, IsProbabilityMeasure (ν N j)],
      (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
      ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ)-2)/2 → 0 < C₀ →
      (∀ᶠ N in atTop, (Fintype.card (ι N) : ℝ) ≤ C₀*(N : ℝ)^κ) →
      inProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereMenuDistance μ β (ν N) (T N)) 1) ∧
  (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
      (R : ℕ → Type v) [∀ N, MeasurableSpace (R N)]
      (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
      (ν : ∀ N, R N → ι N → Measure (Vector N)),
      (∀ N j, Measurable (fun r => ν N r j)) →
      ∀ [∀ N r j, IsProbabilityMeasure (ν N r j)],
      (∀ N, 2 ≤ N → ∀ r j, ∀ᵐ y ∂ν N r j, OnSphere y) →
      ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ)-2)/2 → 0 < C₀ →
      (∀ᶠ N in atTop, (Fintype.card (ι N) : ℝ) ≤ C₀*(N : ℝ)^κ) →
      inProbability (fun N => (ρ N).prod (sphereFieldLaw N μ))
        (fun N z => sphereMenuDistance μ β (ν N z.1) (T N) z.2) 1) ∧
  (∀ (κ : ∀ N, Kernel (SphereField N μ) (Vector N)) [∀ N, IsMarkovKernel (κ N)],
      (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
      littleLogInProbability (fun N => sphereFieldLaw N μ)
        (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N)) →
      inProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereIntervalDistance μ β (T N) (κ N)) 1) ∧
  (∀ (κ : ∀ N, Kernel (SphereField N μ) (Vector N)) [∀ N, IsMarkovKernel (κ N)],
      (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
      littleLog (fun N => fieldMutualInformation (sphereFieldLaw N μ) (κ N)) →
      inProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereIntervalDistance μ β (T N) (κ N)) 1)

end SlowEquilibrationCondensedSource

namespace SlowEquilibration.PalomarCondensed
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sphereField_eq (N : ℕ) (μ : SlowEquilibrationCondensedSource.FiniteMixture) :
    SlowEquilibrationCondensedSource.SphereField N μ =
      SourceMixedCountCapturePackage.SphereField N (toLibrary μ) := rfl

theorem sphereFieldLaw_eq (N : ℕ) (μ : SlowEquilibrationCondensedSource.FiniteMixture) :
    SlowEquilibrationCondensedSource.sphereFieldLaw N μ =
      SourceMixedCountCapturePackage.sphereFieldLaw N (toLibrary μ) := rfl

theorem sphereLift_eq {N : ℕ} (μ : SlowEquilibrationCondensedSource.FiniteMixture) :
    SlowEquilibrationCondensedSource.sphereLift (N := N) μ =
      SourceMixedCountCapturePackage.sphereLift (N := N) (toLibrary μ) := rfl

/-- The selected continuous linear lift always represents the exact displayed spherical field. -/
theorem sphereFieldMap_sphereLift {N : ℕ} (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (H : SlowEquilibrationCondensedSource.SphereField N μ) :
    SlowEquilibrationCondensedSource.sphereFieldMap μ
      (SlowEquilibrationCondensedSource.sphereLift μ H) = H := by
  exact SphericalEffectiveField.project_lift _ _ _

private theorem representative_field_eq {N : ℕ}
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (H : SlowEquilibrationCondensedSource.SphereField N μ) :
    SphericalModel.fieldOfMixture (toLibrary μ)
      (SphericalFieldKernels.coefficientLift (toLibrary μ)
        (SourceMixedCountCapturePackage.sphereRepresentative (toLibrary μ) H)) =
      SlowEquilibrationCondensedSource.field μ (SlowEquilibrationCondensedSource.sphereLift μ H) := by
  exact SphericalFieldKernels.lifted_field_eq (toLibrary μ)
    (SlowEquilibrationCondensedSource.sphereLift μ H)

private theorem representative_restrict_eq {N : ℕ}
    (μ : SlowEquilibrationCondensedSource.FiniteMixture)
    (H : SlowEquilibrationCondensedSource.SphereField N μ) :
    SourceMixedCountCapturePackage.sphereRestriction (toLibrary μ)
      (SourceMixedCountCapturePackage.sphereRepresentative (toLibrary μ) H) = H := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change SphericalModel.fieldOfMixture (toLibrary μ)
    (SphericalFieldKernels.coefficientLift (toLibrary μ)
      (SourceMixedCountCapturePackage.sphereRepresentative (toLibrary μ) H)) x.val = H.val x
  rw [representative_field_eq]
  exact congrArg (fun K : SlowEquilibrationCondensedSource.SphereField N μ => K.val x)
    (sphereFieldMap_sphereLift μ H)

private theorem sphere_distance_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (H : SlowEquilibrationCondensedSource.SphereField N μ)
    (ν : Measure (SlowEquilibrationCondensedSource.Vector N))
    (hν : ∀ᵐ y ∂ν, SlowEquilibrationCondensedSource.OnSphere y) :
    SlowEquilibrationCondensedSource.distance μ β t
        (SlowEquilibrationCondensedSource.sphereLift μ H) ν =
      SlowEquilibration.totalVariation
        (SphericalMenuReduction.physicalSemigroup (toLibrary μ) β
          (SourceMixedCountCapturePackage.sphereRepresentative (toLibrary μ) H) t ∘ₘ ν)
        (SphericalFieldKernels.gibbsKernel (toLibrary μ) β
          (SourceMixedCountCapturePackage.sphereRepresentative (toLibrary μ) H)) := by
  unfold SlowEquilibrationCondensedSource.distance
  rw [evolvedLaw_eq hN μ β t _ ν hν, SphericalFieldKernels.gibbsKernel_apply]
  have hK :
      SphericalDynamics.mixedTransitionKernel (toLibrary μ)
        (SlowEquilibrationCondensedSource.sphereLift μ H) β t ∘ₘ ν =
      SphericalMenuReduction.physicalSemigroup (toLibrary μ) β
        (SourceMixedCountCapturePackage.sphereRepresentative (toLibrary μ) H) t ∘ₘ ν := by
    apply Measure.comp_congr
    filter_upwards [hν] with y hy
    exact SphericalRotationCovariance.mixedTransitionKernel_congr_onSphere hN
      (toLibrary μ) _ _ β
      (fun z _ => (congrFun (representative_field_eq μ H) z).symm) t y hy
  have hπ :
      SlowEquilibrationCondensedSource.gibbsLaw μ β
        (SlowEquilibrationCondensedSource.sphereLift μ H) =
      SphericalModel.mixtureGibbsLaw (toLibrary μ) β
        (SphericalFieldKernels.coefficientLift (toLibrary μ)
          (SourceMixedCountCapturePackage.sphereRepresentative (toLibrary μ) H)) := by
    change SphericalModel.gibbsLaw N β (SlowEquilibrationCondensedSource.field μ _) =
      SphericalModel.gibbsLaw N β (SphericalModel.fieldOfMixture (toLibrary μ) _)
    rw [representative_field_eq]
  exact congrArg₂ SlowEquilibration.totalVariation hK hπ

theorem sphereIntervalDistance_eq {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (SlowEquilibrationCondensedSource.SphereField N μ)
      (SlowEquilibrationCondensedSource.Vector N))
    (H : SlowEquilibrationCondensedSource.SphereField N μ)
    (hκ : ∀ᵐ y ∂κ H, SlowEquilibrationCondensedSource.OnSphere y) :
    SlowEquilibrationCondensedSource.sphereIntervalDistance μ β T κ H =
      SourceMixedCountCapturePackage.sphereIntervalDistance (toLibrary μ) β T κ H := by
  unfold SlowEquilibrationCondensedSource.sphereIntervalDistance
    SlowEquilibrationCondensedSource.intervalDistance
    SourceMixedCountCapturePackage.sphereIntervalDistance SphericalFieldKernels.intervalDistance
  simp only [Kernel.comap_apply, representative_restrict_eq]
  apply congrArg sInf
  apply congrArg (fun f : ℝ → ℝ => f '' Icc 0 (T : ℝ))
  funext t
  exact sphere_distance_eq hN μ β t.toNNReal H (κ H) hκ

private theorem menuMixture_support {N : ℕ} {ι : Type*} [Fintype ι]
    (ν : ι → Measure (SlowEquilibrationCondensedSource.Vector N))
    (hν : ∀ j, ∀ᵐ y ∂ν j, SlowEquilibrationCondensedSource.OnSphere y)
    (w : SlowEquilibrationCondensedSource.MenuWeights ι) :
    ∀ᵐ y ∂SlowEquilibrationCondensedSource.menuMixture ν w,
      SlowEquilibrationCondensedSource.OnSphere y := by
  classical
  have hs (s : Finset ι) : ∀ᵐ y ∂∑ j ∈ s, ENNReal.ofReal (w.val j) • ν j,
      SlowEquilibrationCondensedSource.OnSphere y := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, ae_add_measure_iff]
      exact ⟨Measure.ae_smul_measure (hν j) _, ih⟩
  exact hs Finset.univ

theorem sphereMenuDistance_eq {N : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (hN : 1 ≤ N) (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ)
    (ν : ι → Measure (SlowEquilibrationCondensedSource.Vector N))
    [∀ j, IsProbabilityMeasure (ν j)]
    (hν : ∀ j, ∀ᵐ y ∂ν j, SlowEquilibrationCondensedSource.OnSphere y)
    (T : ℝ≥0) (H : SlowEquilibrationCondensedSource.SphereField N μ) :
    SlowEquilibrationCondensedSource.sphereMenuDistance μ β ν T H =
      SourceMixedCountCapturePackage.sphereMenuDistance (toLibrary μ) β ν T H := by
  unfold SlowEquilibrationCondensedSource.sphereMenuDistance
    SourceMixedCountCapturePackage.sphereMenuDistance
  rw [SphericalMenuReduction.physicalMenuDistance_eq_joint_inf hN]
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨w, t, ht, hr⟩
    exact ⟨w, t, ht, hr.trans (sphere_distance_eq hN μ β t H _ (menuMixture_support ν hν w))⟩
  · rintro ⟨w, t, ht, hr⟩
    exact ⟨w, t, ht, hr.trans (sphere_distance_eq hN μ β t H _ (menuMixture_support ν hν w)).symm⟩

theorem fieldMutualInformation_eq {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]
    (d : Measure D) (κ : Kernel D X) :
    SlowEquilibrationCondensedSource.fieldMutualInformation d κ = endpointMutualInformation d κ := rfl

universe u v

/-- All condensed initial-law conclusions follow conditionally from exactly the same two
explicit literature premises. Information and independence concern the actual spherical field. -/
theorem source_all_initial_spherical
    (μ : SlowEquilibrationCondensedSource.FiniteMixture) {β x Q : ℝ}
    (h : SlowEquilibrationCondensedSource.Certificate μ β x Q)
    (hChen : SlowEquilibrationCondensedSource.Chen2013FiniteParisi)
    (hLemma22 : ∀ μ : SlowEquilibrationCondensedSource.FiniteMixture, ∀ β : ℝ,
      SlowEquilibrationCondensedSource.PressureLowerTails μ β) :
    ∃ γ : ℝ, 0 < γ ∧ SlowEquilibrationCondensedSource.AllInitialConclusions.{u,v} μ β γ := by
  have hL : ∀ μ : SlowEquilibration.FiniteMixture, ∀ β : ℝ,
      LiteratureSubagBandLowerComplete.PressureLowerTails μ β := by
    intro ν b
    exact (pressureLowerTails_iff (ofLibrary ν) b).mp (hLemma22 (ofLibrary ν) b)
  obtain ⟨γ, hγ, hu, _hs, hp, hr, hm, hrm, hkl, hi⟩ :=
    LiteratureSubagSlabTails.finiteMixture_all_initial_spherical_of_chen_and_lemma22.{u,v}
      (toLibrary μ) ((certificate_iff μ β x Q).mp h) (chen_iff.mp hChen) hL
  refine ⟨γ, hγ, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro ε hε
    apply (hu ε hε).congr'
    filter_upwards [] with n
    congr 1
    ext J
    change (ε ≤ ‖SourceReductionConsumerAsymptotic.originalUniformIntervalDistance
      (toLibrary μ) β (SlowEquilibrationCondensedSource.exponentialHorizon γ (n+2)) J - 1‖) ↔
      (ε ≤ ‖SlowEquilibrationCondensedSource.intervalDistance μ β
        (SlowEquilibrationCondensedSource.exponentialHorizon γ (n+2)) J
        (SlowEquilibrationCondensedSource.sphereLaw (n+2))-1‖)
    rw [uniform_intervalDistance_eq (show 1 ≤ n+2 by omega) μ β _ J]
  · intro ε hε
    apply (hp ε hε).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (prescribedFailure_eq hN μ β γ ε).symm
  · intro Ω _ P _ J ν hJ hν hind hsphere ε hε
    apply (hr Ω P J ν hJ hν hind hsphere ε hε).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    apply measureReal_congr
    filter_upwards [hsphere N hN] with ω hω
    rw [intervalDistance_eq hN μ β _ _ _ hω]
    rfl
  · intro ι _ _ ν _ hν κ C₀ hκ hκα hC₀ hcard ε hε
    apply (hm ι ν hν κ C₀ hκ hκα hC₀ hcard ε hε).congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    congr 1
    ext H
    change (ε ≤ ‖SourceMixedCountCapturePackage.sphereMenuDistance (toLibrary μ) β (ν N)
      (SlowEquilibrationCondensedSource.exponentialHorizon γ N) H - 1‖) ↔
      (ε ≤ ‖SlowEquilibrationCondensedSource.sphereMenuDistance μ β (ν N)
        (SlowEquilibrationCondensedSource.exponentialHorizon γ N) H - 1‖)
    rw [sphereMenuDistance_eq (show 1 ≤ N by omega) μ β (ν N) (hν N hN) _ H]
  · intro ι _ _ R _ ρ _ ν hν _ hs κ C₀ hκ hκα hC₀ hcard ε hε
    apply (hrm ι R ρ ν hν hs κ C₀ hκ hκα hC₀ hcard ε hε).congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    congr 1
    ext z
    change (ε ≤ ‖SourceMixedCountCapturePackage.sphereMenuDistance (toLibrary μ) β (ν N z.1)
      (SlowEquilibrationCondensedSource.exponentialHorizon γ N) z.2 - 1‖) ↔
      (ε ≤ ‖SlowEquilibrationCondensedSource.sphereMenuDistance μ β (ν N z.1)
        (SlowEquilibrationCondensedSource.exponentialHorizon γ N) z.2 - 1‖)
    rw [sphereMenuDistance_eq (show 1 ≤ N by omega) μ β (ν N z.1) (hs N hN z.1) _ z.2]
  · intro κ _ hs hKL ε hε
    apply (hkl κ hs hKL ε hε).congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    congr 1
    ext H
    change (ε ≤ ‖SourceMixedCountCapturePackage.sphereIntervalDistance (toLibrary μ) β
      (SlowEquilibrationCondensedSource.exponentialHorizon γ N) (κ N) H - 1‖) ↔
      (ε ≤ ‖SlowEquilibrationCondensedSource.sphereIntervalDistance μ β
        (SlowEquilibrationCondensedSource.exponentialHorizon γ N) (κ N) H - 1‖)
    rw [sphereIntervalDistance_eq (show 1 ≤ N by omega) μ β _ (κ N) H (hs N hN H)]
  · intro κ _ hs hI ε hε
    apply (hi κ hs hI ε hε).congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    congr 1
    ext H
    change (ε ≤ ‖SourceMixedCountCapturePackage.sphereIntervalDistance (toLibrary μ) β
      (SlowEquilibrationCondensedSource.exponentialHorizon γ N) (κ N) H - 1‖) ↔
      (ε ≤ ‖SlowEquilibrationCondensedSource.sphereIntervalDistance μ β
        (SlowEquilibrationCondensedSource.exponentialHorizon γ N) (κ N) H - 1‖)
    rw [sphereIntervalDistance_eq (show 1 ≤ N by omega) μ β _ (κ N) H (hs N hN H)]

end SlowEquilibration.PalomarCondensed
