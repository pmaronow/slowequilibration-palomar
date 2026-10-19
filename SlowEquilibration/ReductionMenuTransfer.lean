-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionMenuMeasurable
public import SlowEquilibration.ReductionEndpointTransfer

/-! The genuine finite-menu band error and source capture transfer.
The probability bound is obtained from actual evolved masses, with no
assumed total-variation or optimizing-weight estimate. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionFiniteMenu
open MeasureTheory ProbabilityTheory Set Filter
open ReductionJointInformation ReductionEndpointTransfer VaryingProbability
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι Ω X : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω] [MeasurableSpace X]

def menuError (μ : ι → Kernel Ω X) (K : Kernel (Ω × X) X)
    (B : Set (Ω × X)) (ω : Ω) : ℝ := ∑ j, conditionalMass (μ j) K B ω

def menuMaxError (μ : ι → Kernel Ω X) (K : Kernel (Ω × X) X)
    (B : Set (Ω × X)) (ω : Ω) : ℝ := ⨆ j, conditionalMass (μ j) K B ω

lemma menuMaxError_le_sum (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K] (B : Set (Ω × X)) (ω : Ω) :
    menuMaxError μ K B ω ≤ menuError μ K B ω := by
  apply ciSup_le
  intro j
  change (evolvedKernel (μ j) K ω).real (Prod.mk ω ⁻¹' B) ≤
    ∑ i, (evolvedKernel (μ i) K ω).real (Prod.mk ω ⁻¹' B)
  exact Finset.single_le_sum (f := fun i => (evolvedKernel (μ i) K ω).real (Prod.mk ω ⁻¹' B))
    (fun i _ => measureReal_nonneg) (Finset.mem_univ j)

lemma menuError_nonneg (μ : ι → Kernel Ω X) (K : Kernel (Ω × X) X)
    (B : Set (Ω × X)) (ω : Ω) : 0 ≤ menuError μ K B ω :=
  Finset.sum_nonneg (fun j _ => measureReal_nonneg)

lemma menuMaxError_nonneg (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K] (B : Set (Ω × X)) (ω : Ω) :
    0 ≤ menuMaxError μ K B ω := by
  have hb : BddAbove (range (fun j => conditionalMass (μ j) K B ω)) :=
    ⟨1,by rintro _ ⟨j,rfl⟩; exact measureReal_le_one⟩
  exact (show 0 ≤ conditionalMass (μ (Classical.arbitrary ι)) K B ω from measureReal_nonneg).trans
    (le_ciSup hb _)

lemma menuMaxError_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) : Integrable (menuMaxError μ K B) d := by
  have hm : Measurable (menuMaxError μ K B) :=
    Measurable.iSup (fun j => conditionalMass_measurable (μ j) K hB)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs,abs_of_nonneg (menuMaxError_nonneg μ K B ω)]
  exact ciSup_le (fun j => measureReal_le_one)

lemma menuError_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) : Integrable (menuError μ K B) d := by
  exact integrable_finsetSum _ (fun j _ => conditionalMass_integrable d (μ j) K hB)

theorem menuError_integral_eq_sum (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) :
    (∫ ω, menuError μ K B ω ∂d) = ∑ j, ∫ ω, conditionalMass (μ j) K B ω ∂d := by
  exact integral_finsetSum _ (fun j _ => conditionalMass_integrable d (μ j) K hB)

theorem menuMaxError_integral_le_sum (d : Measure Ω) [IsProbabilityMeasure d]
    (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) :
    (∫ ω, menuMaxError μ K B ω ∂d) ≤ ∑ j, ∫ ω, conditionalMass (μ j) K B ω ∂d :=
  (integral_mono (menuMaxError_integrable d μ K hB) (menuError_integrable d μ K hB)
    (menuMaxError_le_sum μ K B)).trans_eq (menuError_integral_eq_sum d μ K hB)

/-- A prescribed initial law has the actual common averaged endpoint
mass supplied by the source Haar equal-mass theorem. The state type may
be the sphere itself, so the premise does not assert off-sphere invariance. -/
theorem prescribed_mass_integral_eq (d : Measure Ω) [IsProbabilityMeasure d]
    (ν : Measure X) [IsProbabilityMeasure ν] (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) {q : ℝ}
    (hequal : ∀ x : X, (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d)=q) :
    (∫ ω, conditionalMass (Kernel.const Ω ν) K B ω ∂d)=q := by
  have h := reference_mass_eq_of_equal_mass d (Kernel.const Ω ν) K hB hequal
  have hc : (Kernel.const Ω ν) ∘ₘ d=ν := by
    change d.bind (fun _ => ν)=ν
    rw [Measure.bind_const,measure_univ,one_smul]
  rw [hc] at h
  have hi := retained_joint_mass_eq_integral d (Kernel.const Ω ν) K hB
  rw [Measure.compProd_const] at hi
  exact hi.symm.trans h

theorem prescribed_menuError_integral_eq (d : Measure Ω) [IsProbabilityMeasure d]
    (ν : ι → Measure X) [∀ j, IsProbabilityMeasure (ν j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) {q : ℝ}
    (hequal : ∀ x : X, (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d)=q) :
    (∫ ω, menuError (fun j => Kernel.const Ω (ν j)) K B ω ∂d) = (Fintype.card ι)*q := by
  rw [menuError_integral_eq_sum d _ K hB]
  simp_rw [prescribed_mass_integral_eq d _ K hB hequal]
  simp

theorem menu_endpoint_measurable [MeasurableSpace.CountablyGenerated X]
    (μ : ι → Kernel Ω X) [∀ j, IsMarkovKernel (μ j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    (π : Kernel Ω X) [IsMarkovKernel π] :
    Measurable (fun ω => menuDistance (fun j => evolvedKernel (μ j) K ω) (π ω)) :=
  menuDistance_measurable _ _ (fun j => (evolvedKernel (μ j) K).measurable) π.measurable

section Varying
variable {Ωₙ Xₙ ιₙ : ℕ → Type*}
  [∀ N, MeasurableSpace (Ωₙ N)] [∀ N, MeasurableSpace (Xₙ N)]
  [∀ N, Fintype (ιₙ N)] [∀ N, Nonempty (ιₙ N)]

/-- Uniform separation over every simplex weight, from the original
capture premise and vanishing genuine expected menu error. -/
theorem menu_endpoint_separation_of_capture
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ : ∀ N, ιₙ N → Kernel (Ωₙ N) (Xₙ N)) [∀ N j, IsMarkovKernel (μ N j)]
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ωₙ N × Xₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, ℝ → Set (Ωₙ N × Xₙ N)) (hB : ∀ N M, MeasurableSet (B N M))
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (herror : ∀ M : ℝ, 0 < M →
      Tendsto (fun N => ∫ ω, menuError (μ N) (K N) (B N M) ω ∂d N) atTop (𝓝 0)) :
    InProbability d (fun N ω => menuDistance (fun j => evolvedKernel (μ N j) (K N) ω) (π N ω)) 1 := by
  apply VaryingProbability.testing_band_union d _
    (fun N M ω => (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ)
    (fun N M => menuError (μ N) (K N) (B N M))
  · intro N ω
    exact menuDistance_le_one _ _
  · intro N M hM ω
    exact measureReal_nonneg
  · intro N M hM ω
    exact menuError_nonneg _ _ _ _
  · intro N M hM
    have hm := (Kernel.measurable_kernel_prodMk_left (κ := π N) (hB N M).compl).ennreal_toReal
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall (fun ω => by
      change ‖(π N ω).real (Prod.mk ω ⁻¹' (B N M)ᶜ)‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  · exact hcapture
  · intro M hM
    exact inProbability_zero_of_integral_tendsto_zero d _
      (fun N => menuError_nonneg _ _ _) (fun N => menuError_integrable (d N) _ _ (hB N M)) (herror M hM)
  · intro N M hM ω
    exact menuDistance_separation _ _ (measurable_prodMk_left (hB N M))

/-- Source prescribed-menu conclusion under its literal K_N q_N,M → 0
condition, derived from the common averaged mass and original capture. -/
theorem prescribed_menu_endpoint_separation
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (ν : ∀ N, ιₙ N → Measure (Xₙ N)) [∀ N j, IsProbabilityMeasure (ν N j)]
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ωₙ N × Xₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, ℝ → Set (Ωₙ N × Xₙ N)) (hB : ∀ N M, MeasurableSet (B N M))
    (q : ℕ → ℝ → ℝ)
    (hequal : ∀ N M x, (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N M) ∂d N)=q N M)
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (hsize : ∀ M : ℝ, 0 < M → Tendsto (fun N => (Fintype.card (ιₙ N):ℝ)*q N M) atTop (𝓝 0)) :
    InProbability d (fun N ω => menuDistance
      (fun j => evolvedKernel (Kernel.const (Ωₙ N) (ν N j)) (K N) ω) (π N ω)) 1 := by
  apply menu_endpoint_separation_of_capture d (fun N j => Kernel.const (Ωₙ N) (ν N j)) π K B hB hcapture
  intro M hM
  simpa only [prescribed_menuError_integral_eq _ _ _ (hB _ _) (hequal _ _)] using hsize M hM

end Varying
end SlowEquilibration.ReductionFiniteMenu
