module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalStationarySDE
public import SlowEquilibration.SphericalTransitionRotation
public import Mathlib.Probability.Process.FiniteDimensionalLaws

@[expose] public section

/-! # The actual mixed SDE transition after an observed finite history

The history transition identity is proved from genuine Brownian future
independence, actual restart uniqueness, and the literal Picard sample.
It is the finite-dimensional provider for path-law covariance.
-/
namespace SlowEquilibration.SphericalRotationCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalStationarySDE
open SphericalAging SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}

lemma kernel_section_measurable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (κ : Kernel A B) [IsSFiniteKernel κ] {S : Set (A × B)} (hS : MeasurableSet S) :
    Measurable (fun a => κ a (Prod.mk a ⁻¹' S)) := by
  have hm := (Kernel.id ×ₖ κ).measurable_coe hS
  simpa only [Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hS] using hm

/-- Ordinary composition-product transport. The actual kernel covariance
provider is used below to instantiate the pointwise measure equality. -/
lemma compProd_map_prodMap {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (ρ : Measure A) [SFinite ρ]
    (κ : Kernel A B) [IsSFiniteKernel κ] (η : Kernel C D) [IsSFiniteKernel η]
    (f : A → C) (hf : Measurable f) (g : B → D) (hg : Measurable g)
    (he : ∀ᵐ a ∂ρ, (κ a).map g=η (f a)) :
    (ρ ⊗ₘ κ).map (Prod.map f g) = ρ.map f ⊗ₘ η := by
  ext S hS
  rw [Measure.map_apply (hf.prodMap hg) hS,Measure.compProd_apply ((hf.prodMap hg) hS),
    Measure.compProd_apply hS,lintegral_map (kernel_section_measurable η hS) hf]
  apply lintegral_congr_ae
  filter_upwards [he] with a ha
  rw [← ha,Measure.map_apply hg (hS.preimage measurable_prodMk_left)]
  rfl

/-- The next state after a genuinely observed history has the literal
physical transition as its conditional kernel. No Markov hypothesis is
supplied: both restart and future independence are actual SDE theorems. -/
theorem history_nextState_law (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) (s t : ℝ≥0)
    {A : Type*} [MeasurableSpace A] (Z : VectorBrownian.Space N → A)
    (hZ : Measurable[NullAugmentation.augment (VectorBrownian.filtration N)
      (VectorBrownian.law N) s] Z)
    (point : A → Vector N) (hpoint : Measurable point)
    (hwaiting : (fun ω => point (Z ω)) =ᵐ[VectorBrownian.law N] mixedProcess μ J β x s) :
    (VectorBrownian.law N).map (fun ω => (Z ω,mixedProcess μ J β x (s+t) ω)) =
      ((VectorBrownian.law N).map Z) ⊗ₘ (mixedTransitionKernel μ J β t).comap point hpoint := by
  let P := VectorBrownian.law N
  have hZm : Measurable Z := hZ.mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) P).le s) le_rfl
  let ρ := P.map Z
  letI : IsProbabilityMeasure ρ := by dsimp [ρ,P]; infer_instance
  let φ : VectorBrownian.Space N → A × VectorBrownian.Space N :=
    fun ω => (Z ω,BrownianFuturePath.future s ω)
  have hφ : MeasurePreserving φ P (ρ.prod P) :=
    BrownianFutureFiltered.waiting_future_measurePreserving s Z hZ
  let χ : A × VectorBrownian.Space N → A × Vector N :=
    fun q => (q.1,sample μ J β t (point q.1,q.2))
  have hχ : Measurable χ := measurable_fst.prodMk
    ((sample_measurable μ J β t).comp ((hpoint.comp measurable_fst).prodMk measurable_snd))
  have hrestart := FixedCoefficients.future_restart
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec
    (mixedCoefficientBounds μ J β) x s t
  have he : (fun ω => (Z ω,mixedProcess μ J β x (s+t) ω)) =ᵐ[P] χ ∘ φ := by
    filter_upwards [hrestart,hwaiting] with ω hr hw
    dsimp only [χ,φ,Function.comp_def,sample]
    rw [hw]
    exact congrArg (Prod.mk (Z ω)) hr
  calc
    _ = P.map (χ ∘ φ) := Measure.map_congr he
    _ = (ρ.prod P).map χ := by
      rw [← hφ.map_eq,Measure.map_map hχ hφ.measurable]
    _ = ρ ⊗ₘ (mixedTransitionKernel μ J β t).comap point hpoint := by
      ext B hB
      rw [Measure.map_apply hχ hB,Measure.prod_apply (hχ hB),Measure.compProd_apply hB]
      apply lintegral_congr
      intro z
      rw [Kernel.comap_apply]
      rw [← sample_conditional_law μ J β t (point z)]
      have hsample : Measurable (fun ω => sample μ J β t (point z,ω)) :=
        (sample_measurable μ J β t).comp measurable_prodMk_left
      rw [Measure.map_apply hsample
        (hB.preimage measurable_prodMk_left)]
      rfl

end
end SlowEquilibration.SphericalRotationCovariance
