module
public import FourPapersCommon.MixedUniformQuadratic
public import FourPapersCommon.MixedQuadraticTail
public import FourPapersCommon.MixedSchemeStrictReduction

@[expose] public section

/-! Genuine near-optimal mixed Guerra interpolation convergence.  The
probability spaces may vary with system size.  All constrained-pressure
estimates are supplied by proved actual-model theorems, including negative
overlaps, the zero initial overlap, and redundant scheme levels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open SpinGlass SpinGlass.Targets
open scoped Topology
namespace FourPapersCommon
universe u
set_option maxHeartbeats 1000000

theorem mixed_nearOptimal_interpolation_all_models
    (ξ : AdmissibleEvenMixture) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k) (h : ℝ),
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε →
      (∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) →
      ∀ (Ωn : ℕ → Type u) [∀ n, MeasureSpace (Ωn n)]
        [∀ n, IsProbabilityMeasure (ℙ : Measure (Ωn n))],
      ∀ sk : ∀ n, MixedDisorder (Ω := Ωn n) n ξ,
      ∀ t ∈ Icc (0 : ℝ) t₀,
        Tendsto (fun n => guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h (sk n).U t)
          atTop (𝓝 (mixedInterpolationPsi ξ s h t)) := by
  obtain ⟨ε, hε, Hε⟩ := exists_mixed_uniform_quadratic_tolerance ξ ht₀.2
  refine ⟨ε, hε, ?_⟩
  intro k s h hnear hmin Ωn _ _ sk t ht
  obtain ⟨l, _, s', hm, hq, hf, hpsi, hphi, hmin'⟩ :=
    exists_strict_mass_overlap_mixed_reduction ξ s h
  have hnear' : mixedFunctional ξ h (Paper.parisiSchemeMeasure s') ≤ mixedPressure ξ h + ε :=
    hf.trans_le hnear
  obtain ⟨K, hK, HK⟩ := Hε s' h hm hq (hmin' hmin) hnear'
  have hquad : ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ∀ d, 1 ≤ d → d ≤ l + 1 → ∀ v ∈ attainableOverlaps n,
      constrainedPhi n (mixedClockScheme ξ s') (mixedBeta ξ) h (sk n).U d t v ≤
        2 * mixedInterpolationPsi ξ s' h t - (v - s'.q (l + 2 - d)) ^ 2 / K := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro t ht d hd0 hd v hv
    obtain ⟨σ, τ, hστ⟩ := mem_attainableOverlaps.mp hv
    have habs : |v| ≤ 1 := by rw [← hστ]; exact abs_overlap_le_one hn σ τ
    have H := HK (Ωn n) hn (sk n) t ⟨ht.1.le, ht.2.le⟩ (l + 2 - d)
      (by omega) (by omega) v (abs_le.mp habs) ⟨σ, τ, hστ⟩
    simpa only [show l + 2 - (l + 2 - d) = d by omega] using H
  have hm1 : 0 < s'.m 1 := by simpa only [s'.m_zero] using hm 0 (by omega)
  have HU := mixedInterpolation_uniform_of_quadratic_bound Ωn ξ sk s' h hm1 ht₀ hK hquad
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [HU δ hδ] with n hn
  have H := hn t ht
  rw [hpsi t, hphi (Ωn n) n (sk n).U t ⟨ht.1, ht.2.trans ht₀.2.le⟩] at H
  simpa only [Real.dist_eq] using H

end FourPapersCommon
