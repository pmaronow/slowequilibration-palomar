-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalNearOnePairGoodField
public import SlowEquilibration.SphericalTaylorContinuousLaw

/-! Transfer the spherical field bound to the actual disorder-averaged
physical pair law. The measurable good event is built from the two signed
Gaussian spherical suprema, and its complement has an explicit tail. -/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open SlowEquilibration SphericalModel SphericalForm
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit
open SlowEquilibration.PureCapturePhysicalNearOnePairGoodField
open SlowEquilibration.GaussianReplicaKernel
open SlowEquilibration.SphericalTaylorRemainder
open scoped Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SlowEquilibration.PureCapturePhysicalNearOneAverage

theorem physicalFullOverlapLaw_pairCap_le_absolutePair
    (μ : FiniteMixture) (β a : ℝ) (n : ℕ) :
    (physicalFullOverlapLaw (n := n) (m := 2) μ β :
      Measure (FullOverlapCoordinates 2)) (fullPairCapEvent a) ≤
    (((allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β) ×ₖ
      (allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β)) ∘ₘ
      disorderLaw (n+2) μ.maxDegree)
      (absoluteReplicaOverlapEvent a) := by
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  have hpair := GaussianReplicaKernel.pair_hasLaw
    (disorderLaw (n+2) μ.maxDegree) G
    (0 : Fin 2) (1 : Fin 2) (by decide)
  have hsub : physicalFullOverlapCoordinates ⁻¹' fullPairCapEvent a ⊆
      (fun σ : Fin 2 → Vector (n+2) => (σ 0, σ 1)) ⁻¹'
        absoluteReplicaOverlapEvent a := by
    intro σ hσ
    change a < physicalFullOverlapCoordinates σ 0 1 at hσ
    change a ≤ |overlap (σ 0) (σ 1)|
    have hh : a < overlap (σ 0) (σ 1) := by
      simpa [physicalFullOverlapCoordinates] using hσ
    exact hh.le.trans (le_abs_self _)
  change (physicalReplicaLaw (n := n) (m := 2) μ β).map
      physicalFullOverlapCoordinates (fullPairCapEvent a) ≤ _
  rw [Measure.map_apply physicalFullOverlapCoordinates_continuous.measurable
    (fullPairCapEvent_open a).measurableSet]
  calc
    _ ≤ (physicalReplicaLaw (n := n) (m := 2) μ β)
      ((fun σ : Fin 2 → Vector (n+2) => (σ 0, σ 1)) ⁻¹'
        absoluteReplicaOverlapEvent a) := measure_mono hsub
    _ = ((G ×ₖ G) ∘ₘ disorderLaw (n+2) μ.maxDegree)
        (absoluteReplicaOverlapEvent a) := by
      rw [← hpair.map_eq]
      rw [Measure.map_apply
        ((measurable_pi_apply (0 : Fin 2)).prodMk
          (measurable_pi_apply (1 : Fin 2)))
        (absoluteReplicaOverlapEvent_measurable a)]
      rfl

theorem averagedKernelEvent_le_good_plus_bad
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    (d : Measure Ω) [IsProbabilityMeasure d]
    (κ : Kernel Ω V) [IsMarkovKernel κ]
    (E : Set V) (hE : MeasurableSet E)
    (A : Set Ω) (hA : MeasurableSet A)
    {B : ℝ} (hB : 0 ≤ B)
    (hgood : ∀ ω ∈ A, (κ ω).real E ≤ B) :
    (κ ∘ₘ d).real E ≤ B + d.real Aᶜ := by
  have heq : (κ ∘ₘ d).real E = ∫ ω, (κ ω).real E ∂d := by
    rw [Measure.real, Measure.bind_apply hE κ.aemeasurable,
      ← integral_toReal (κ.measurable_coe hE).aemeasurable
        (.of_forall (fun ω => by finiteness))]
    rfl
  rw [heq]
  let f : Ω → ℝ := fun ω => (κ ω).real E
  have hf : Measurable f := (κ.measurable_coe hE).ennreal_toReal
  have hfi : Integrable f d := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact .of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hgi : Integrable (fun ω => B + Aᶜ.indicator (fun _ : Ω => (1 : ℝ)) ω) d :=
    (integrable_const B).add ((integrable_const 1).indicator hA.compl)
  have hpoint (ω : Ω) : f ω ≤ B + Aᶜ.indicator (fun _ : Ω => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_notMem (show ω ∉ Aᶜ from fun h => h hω)]
      exact hgood ω hω
    · have hh : f ω ≤ 1 := measureReal_le_one
      simp [Set.indicator_of_mem (show ω ∈ Aᶜ from hω)]
      linarith
  calc
    ∫ ω, f ω ∂d ≤ ∫ ω, B + Aᶜ.indicator (fun _ : Ω => (1 : ℝ)) ω ∂d :=
      integral_mono hfi hgi hpoint
    _ = B + d.real Aᶜ := by
      rw [integral_add (integrable_const B) ((integrable_const 1).indicator hA.compl),
        integral_const]
      change d.real Set.univ • B + ∫ a, Aᶜ.indicator (1 : Ω → ℝ) a ∂d =
        B + d.real Aᶜ
      rw [integral_indicator_one hA.compl]
      simp

theorem physicalFullOverlapLaw_pairCap_real_le_of_goodField
    (μ : FiniteMixture) {β K : ℝ} (hβ : 0 ≤ β)
    {n : ℕ} (hn : 1 ≤ n)
    (A : Set (Disorder (n+2) μ.maxDegree)) (hA : MeasurableSet A)
    (hfield : ∀ J ∈ A, ∀ x : Vector (n+2),
      ‖x‖^2 = ((n+2 : ℕ) : ℝ) →
      |field (mixtureCoefficients μ) J x| ≤ K*((n+2 : ℕ) : ℝ))
    {a s : ℝ} (ha : 0 < a) (has : a < s) (hs : s < 1) :
    (physicalFullOverlapLaw (n := n) (m := 2) μ β :
      Measure (FullOverlapCoordinates 2)).real (fullPairCapEvent s) ≤
      2*(Real.exp (2*β*K*((n+2 : ℕ) : ℝ)) *
        (4*Real.sqrt ((n+1 : ℕ) : ℝ)*
          (Real.sqrt (1-a^2))^(n-1))) +
      (disorderLaw (n+2) μ.maxDegree).real Aᶜ := by
  let G := allDimensionGibbsKernel (N := n+2) (mixtureCoefficients μ) β
  let d := disorderLaw (n+2) μ.maxDegree
  have hfirst := physicalFullOverlapLaw_pairCap_le_absolutePair μ β s n
  have hfirstR :
      (physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)).real (fullPairCapEvent s) ≤
      ((G ×ₖ G) ∘ₘ d).real (absoluteReplicaOverlapEvent s) :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr hfirst
  have hbound (J : Disorder (n+2) μ.maxDegree) (hJ : J ∈ A) :
      ((G ×ₖ G) J).real (absoluteReplicaOverlapEvent s) ≤
      2*(Real.exp (2*β*K*((n+2 : ℕ) : ℝ)) *
        (4*Real.sqrt ((n+1 : ℕ) : ℝ)*
          (Real.sqrt (1-a^2))^(n-1))) := by
    rw [Kernel.prod_apply, allDimensionGibbsKernel_apply]
    have he : n+1-2 = n-1 := by omega
    simpa only [show n+1+1=n+2 by omega, he] using
      physical_pair_near_one_le_of_field_bound μ
        (n := n+1) (by omega) hβ J (hfield J hJ) ha has hs
  have hsecond := averagedKernelEvent_le_good_plus_bad d (G ×ₖ G)
    (absoluteReplicaOverlapEvent s) (absoluteReplicaOverlapEvent_measurable s)
    A hA (by positivity) hbound
  exact hfirstR.trans hsecond

theorem sphericalFieldSupremum_measurable {n P : ℕ}
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    {σ : ℝ} (hσ : |σ| = 1) :
    Measurable (fun J : Disorder (n+1) P => sphericalFieldSupremum c σ J) := by
  have hcont : Continuous (fun g : EuclideanDisorder (n+1) P =>
      ⨆ x : SpinSphere n, inner ℝ (σ • fieldFeature c (x : Vector (n+1))) g) :=
    (signedFeatureSupremum_lipschitz c hc hσ).continuous
  have heq : (fun J : Disorder (n+1) P => sphericalFieldSupremum c σ J) =
      (fun g : EuclideanDisorder (n+1) P =>
        ⨆ x : SpinSphere n, inner ℝ (σ • fieldFeature c (x : Vector (n+1))) g) ∘
      euclideanDisorder := by
    funext J
    simpa only [Function.comp_apply, unpack_euclideanDisorder] using
      (signedFeatureSupremum_eq c σ (euclideanDisorder J)).symm
  rw [heq]
  exact hcont.measurable.comp (euclideanDisorder_measurable (n+1) P)

def physicalFieldGoodSet (μ : FiniteMixture) (n : ℕ) (K : ℝ) :
    Set (Disorder (n+2) μ.maxDegree) :=
  {J | sphericalFieldSupremum (mixtureCoefficients μ) 1 J <
        K*((n+2 : ℕ) : ℝ) ∧
      sphericalFieldSupremum (mixtureCoefficients μ) (-1) J <
        K*((n+2 : ℕ) : ℝ)}

theorem physicalFieldGoodSet_measurable (μ : FiniteMixture) (n : ℕ)
    (K : ℝ) : MeasurableSet (physicalFieldGoodSet μ n K) := by
  unfold physicalFieldGoodSet
  exact (measurableSet_lt
    (sphericalFieldSupremum_measurable (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) (by norm_num : |(1 : ℝ)|=1))
    measurable_const).inter
    (measurableSet_lt
      (sphericalFieldSupremum_measurable (mixtureCoefficients μ)
        (mixtureCoefficients_nonnegative μ) (by norm_num : |(-1 : ℝ)|=1))
      measurable_const)

theorem physicalFieldGoodSet_uniform (μ : FiniteMixture) (n : ℕ)
    (K : ℝ) (J : Disorder (n+2) μ.maxDegree)
    (hJ : J ∈ physicalFieldGoodSet μ n K)
    (x : Vector (n+2))
    (hx : ‖x‖^2 = ((n+2 : ℕ) : ℝ)) :
    |field (mixtureCoefficients μ) J x| ≤ K*((n+2 : ℕ) : ℝ) := by
  let v : SpinSphere (n+1) := ⟨x, by
    rw [Metric.mem_sphere, dist_zero_right, ← hx, Real.sqrt_sq (norm_nonneg _)]⟩
  have hp := signed_field_le_supremum (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) (by norm_num : |(1 : ℝ)|=1) J v
  have hm := signed_field_le_supremum (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) (by norm_num : |(-1 : ℝ)|=1) J v
  have hh := hJ
  change sphericalFieldSupremum (mixtureCoefficients μ) 1 J < _ ∧
    sphericalFieldSupremum (mixtureCoefficients μ) (-1) J < _ at hh
  have hp' : field (mixtureCoefficients μ) J x ≤
      sphericalFieldSupremum (mixtureCoefficients μ) 1 J := by
    simpa only [one_mul] using hp
  have hm' : -field (mixtureCoefficients μ) J x ≤
      sphericalFieldSupremum (mixtureCoefficients μ) (-1) J := by
    simpa only [neg_one_mul] using hm
  have hu : field (mixtureCoefficients μ) J x ≤ K*((n+2 : ℕ) : ℝ) := by
    exact hp'.trans hh.1.le
  have hl : -(K*((n+2 : ℕ) : ℝ)) ≤ field (mixtureCoefficients μ) J x := by
    have h := hm'.trans hh.2.le
    linarith
  exact abs_le.mpr ⟨hl, hu⟩

theorem physicalFieldGoodSet_complement_bound
    (μ : FiniteMixture) (n : ℕ)
    (hcov : 0 < covariancePolynomial (mixtureCoefficients μ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (disorderLaw (n+2) μ.maxDegree).real
      (physicalFieldGoodSet μ n
        (Real.sqrt (spatialVariance (mixtureCoefficients μ))+t))ᶜ ≤
      2*Real.exp (-(t^2*((n+2 : ℕ) : ℝ))/
        (2*covariancePolynomial (mixtureCoefficients μ) 1)) := by
  let c := mixtureCoefficients μ
  let K := Real.sqrt (spatialVariance c)+t
  let d := disorderLaw (n+2) μ.maxDegree
  let Eplus : Set (Disorder (n+2) μ.maxDegree) :=
    {J | K*((n+2 : ℕ) : ℝ) ≤ sphericalFieldSupremum c 1 J}
  let Eminus : Set (Disorder (n+2) μ.maxDegree) :=
    {J | K*((n+2 : ℕ) : ℝ) ≤ sphericalFieldSupremum c (-1) J}
  have hcomp : (physicalFieldGoodSet μ n K)ᶜ = Eplus ∪ Eminus := by
    ext J
    change (¬ (sphericalFieldSupremum c 1 J < K*((n+2 : ℕ) : ℝ) ∧
      sphericalFieldSupremum c (-1) J < K*((n+2 : ℕ) : ℝ))) ↔
      (K*((n+2 : ℕ) : ℝ) ≤ sphericalFieldSupremum c 1 J ∨
        K*((n+2 : ℕ) : ℝ) ≤ sphericalFieldSupremum c (-1) J)
    simp only [not_and_or, not_lt]
  have hp := sphericalFieldSupremum_upper_tail (n := n+1) c
    (mixtureCoefficients_nonnegative μ) hcov
    (by norm_num : |(1 : ℝ)|=1) ht
  have hm := sphericalFieldSupremum_upper_tail (n := n+1) c
    (mixtureCoefficients_nonnegative μ) hcov
    (by norm_num : |(-1 : ℝ)|=1) ht
  have hpR : d.real Eplus ≤
      Real.exp (-(t^2*((n+2 : ℕ) : ℝ))/(2*covariancePolynomial c 1)) := by
    have hp' := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mpr hp
    change (d Eplus).toReal ≤ _
    simpa only [d, Eplus, K, c, show n+1+1=n+2 by omega,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hp'
  have hmR : d.real Eminus ≤
      Real.exp (-(t^2*((n+2 : ℕ) : ℝ))/(2*covariancePolynomial c 1)) := by
    have hm' := (ENNReal.toReal_le_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mpr hm
    change (d Eminus).toReal ≤ _
    simpa only [d, Eminus, K, c, show n+1+1=n+2 by omega,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hm'
  rw [show Real.sqrt (spatialVariance (mixtureCoefficients μ))+t = K from rfl,
    hcomp]
  exact (measureReal_union_le Eplus Eminus).trans (by linarith)

end SlowEquilibration.PureCapturePhysicalNearOneAverage
