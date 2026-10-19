module
public import FRSB.ConditionalKernelLaw
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section

/-! Genuine joint transition laws with an arbitrary measurable record of
the past. This is the measure-theoretic induction step for finite path laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace FourPapersCommon
variable {State : Type*} [MeasurableSpace State]

theorem joint_transitionLaw_of_restricted {Ω A : Type*}
    (m₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsFiniteMeasure P] (hm₀ : m₀ ≤ mΩ)
    (Y : Ω → A) (hY : Measurable[m₀] Y) (X W : Ω → State)
    (hX : Measurable X) (hW : Measurable W) (ρ : A → State) (hρ : Measurable ρ)
    (hXρ : ∀ sample, X sample = ρ (Y sample))
    (κ : Kernel State State) [IsMarkovKernel κ]
    (hlaw : ∀ E : Set Ω, MeasurableSet[m₀] E →
      (P.restrict E).map W = κ ∘ₘ (P.restrict E).map X) :
    P.map (fun sample => (Y sample, W sample)) = (P.map Y) ⊗ₘ (κ.comap ρ hρ) := by
  have hYg : Measurable Y := hY.mono hm₀ le_rfl
  apply Measure.ext_prod
  intro s t hs ht
  let E := Y ⁻¹' s
  have hE : MeasurableSet[m₀] E := hY hs
  calc
    P.map (fun sample => (Y sample, W sample)) (s ×ˢ t) = (P.restrict E).map W t := by
      rw [Measure.map_apply (hYg.prodMk hW) (hs.prod ht), Measure.map_apply hW ht,
        Measure.restrict_apply (hW ht)]
      congr 1
      ext sample
      simp only [E, mem_preimage, mem_prod]
      exact and_comm
    _ = (κ ∘ₘ (P.restrict E).map X) t := by rw [hlaw E hE]
    _ = ∫⁻ sample in E, κ (X sample) t ∂P := by
      rw [Measure.bind_apply ht κ.aemeasurable,
        lintegral_map (κ.measurable_coe ht) hX]
    _ = ∫⁻ sample in E, κ (ρ (Y sample)) t ∂P :=
      lintegral_congr (fun sample => by rw [hXρ sample])
    _ = ((P.map Y) ⊗ₘ (κ.comap ρ hρ)) (s ×ˢ t) := by
      rw [Measure.compProd_apply_prod hs ht, Measure.restrict_map hYg hs]
      have hmap := lintegral_map (μ := P.restrict E)
        (show Measurable (fun y : A => κ (ρ y) t) from (κ.measurable_coe ht).comp hρ) hYg
      exact hmap.symm

/-- Density transport through a measurable map, when the density depends
only on the image. This needs no injectivity or discrete approximation. -/
theorem map_withDensity_pullback {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) (F : A → B) (hF : Measurable F) (D : B → ℝ≥0∞) (hD : Measurable D) :
    (P.withDensity (fun a => D (F a))).map F = (P.map F).withDensity D := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs),
    withDensity_apply _ hs, Measure.restrict_map hF hs, lintegral_map hD hF]

end FourPapersCommon
