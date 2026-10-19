module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import FourPapersCommon.MixedCoupledGaussianLaw
public import Targets.CoupledOuterExpectation

@[expose] public section

/-! Actual mixed constrained/replica expectations under spectral Gaussian coordinates.
The covariance-independent proof adapts the audited Apache-2.0
Targets.CoupledOuterExpectation, with the genuine mixed disorder record.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real SpinGlass SpinGlass.Targets
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n k : ℕ} {ξ : AdmissibleEvenMixture}
set_option maxHeartbeats 800000

theorem mixed_integrable_coupledGap_outer (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k) (h : ℝ)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d j : ℕ) :
    Integrable (fun p : Ω × (Fin n → ℝ) =>
      coupledGap n s (mixedBeta ξ) (sk.U p.1) h t u d j (coupledOuterField s (mixedBeta ξ) p.2))
      ((ℙ : Measure Ω).prod (piGauss n)) := by
  have hF := (measurable_coupledGap s (mixedBeta ξ) h t u d j).comp
    (f := fun p : EnergySpace n × (Fin n → ℝ) => (p.1, coupledOuterField s (mixedBeta ξ) p.2))
    (by unfold coupledOuterField; fun_prop)
  exact (integrable_mixedCoupledGaussian_pair_iff sk hF).mp
    (integrable_mixedGaussianCoupledGap sk s h hn ht u hu d j)

theorem mixed_integral_gaussianCoupledGap_eq (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k) (h : ℝ)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    (∫ z, mixedGaussianCoupledGap sk s h t u d (k + 1) z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      ∫ ω, coupledGap n s (mixedBeta ξ) (sk.U ω) h t u d (k + 2) 0 ∂ℙ := by
  have hF := (measurable_coupledGap s (mixedBeta ξ) h t u d (k + 1)).comp
    (f := fun p : EnergySpace n × (Fin n → ℝ) => (p.1, coupledOuterField s (mixedBeta ξ) p.2))
    (by unfold coupledOuterField; fun_prop)
  have he := integral_mixedCoupledGaussian_pair sk hF
  change (∫ z, mixedGaussianCoupledGap sk s h t u d (k + 1) z
    ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) = _ at he
  rw [he]
  dsimp only [Function.comp_def]
  rw [integral_prod _ (mixed_integrable_coupledGap_outer sk s h hn ht u hu d (k + 1))]
  apply integral_congr_ae
  filter_upwards with ω
  exact (coupledGap_top_eq_integral s (mixedBeta ξ) (sk.U ω) h u ht hu d hd).symm

theorem mixed_integrable_coupledGap_top (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k) (h : ℝ)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    Integrable (fun ω => coupledGap n s (mixedBeta ξ) (sk.U ω) h t u d (k + 2) 0) ℙ := by
  have H := (mixed_integrable_coupledGap_outer sk s h hn ht u hu d (k + 1)).integral_prod_left
  simpa only [← coupledGap_top_eq_integral s (mixedBeta ξ) _ h u ht hu d hd] using H

/-- The unrestricted top pressure is integrable in the abstract Gaussian disorder. -/
theorem mixed_integrable_coupledCascade_top (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k) (h : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) :
    Integrable (fun ω => coupledCascade n s (mixedBeta ξ) d (coupledBase n (sk.U ω) h t) (k + 2) 0 0) ℙ := by
  obtain ⟨a, D, hD, hprops⟩ := guerra_cascade_continuous_Icc n s (mixedBeta ξ) h (k + 2)
  have hi : Integrable (fun ω => cascadeT n s (mixedBeta ξ) 1 (guerraBase n (sk.U ω) h t) (k + 2) 0) ℙ := by
    refine ((integrable_const a).add
      ((PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian sk.hU).const_mul
        (Fintype.card (Config n)))).mono'
      ((measurable_cascade_top_U s (mixedBeta ξ) h t).comp sk.hU.repr_measurable).aestronglyMeasurable ?_
    filter_upwards with ω
    have hb := (hprops (sk.U ω)).2.1 t ht 0
    simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at hb
    rw [Real.norm_eq_abs]
    exact hb.trans (add_le_add_right (uAbs_le_card_mul_norm n (sk.U ω)) a)
  simpa only [coupledCascade_diag n s (mixedBeta ξ) _ h ht] using hi.const_mul 2

theorem mixed_integrable_constrainedCascade_top (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k) (h : ℝ)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    Integrable (fun ω => coupledCascade n s (mixedBeta ξ) d (constrainedBase n (sk.U ω) h t u) (k + 2) 0 0) ℙ := by
  have H := (mixed_integrable_coupledGap_top sk s h hn ht u hu d hd).add
    (mixed_integrable_coupledCascade_top sk s h ht d)
  simpa only [Pi.add_def, coupledGap, sub_add_cancel] using H

/-- The mean hypothesis in Lemma 2.6 is exactly the pressure gap in Proposition 2.5. -/
theorem mixed_gaussianCoupledGap_mean_eq (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k) (h : ℝ)
    (hn : 0 < n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    (∫ z, mixedGaussianCoupledGap sk s h t u d (k + 1) z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      n * (constrainedPhi n s (mixedBeta ξ) h sk.U d t u - 2 * guerraPhi n s (mixedBeta ξ) h sk.U t) := by
  rw [mixed_integral_gaussianCoupledGap_eq sk s h hn ht u hu d hd]
  simp only [coupledGap]
  rw [integral_sub (mixed_integrable_constrainedCascade_top sk s h hn ht u hu d hd)
    (mixed_integrable_coupledCascade_top sk s h ht d), ← coupledPhi_eq_two_guerraPhi n s (mixedBeta ξ) h sk.U d ht]
  unfold constrainedPhi coupledPhi
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp

theorem mixed_integral_gaussianCoupledEvent_eq (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k) (h : ℝ)
    (hs : 0 < s.m 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    (∫ z, mixedGaussianCoupledEvent sk s h t u d z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      ∫ ω, coupledObservable n s (mixedBeta ξ) (sk.U ω) h t d (overlapEvent n u) (k + 2) 0 0 ∂ℙ := by
  have hF := (measurable_coupledObservable_joint s (mixedBeta ξ) h t d (overlapEvent n u) (k + 1)).comp
    (f := fun p : EnergySpace n × (Fin n → ℝ) =>
      (p.1, (coupledOuterField s (mixedBeta ξ) p.2, coupledOuterField s (mixedBeta ξ) p.2)))
    (by unfold coupledOuterField; fun_prop)
  have hi := (integrable_mixedCoupledGaussian_pair_iff sk hF).mp
    (integrable_mixedGaussianCoupledEvent sk s h hs ht u hu d)
  have he := integral_mixedCoupledGaussian_pair sk hF
  change (∫ z, mixedGaussianCoupledEvent sk s h t u d z
    ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) = _ at he
  rw [he, integral_prod _ hi]
  dsimp only [Function.comp_def]
  simp_rw [← coupledObservable_top_eq_integral s (mixedBeta ξ) _ h t d hd (overlapEvent n u)]

theorem mixed_gaussianCoupledEvent_mean_eq (sk : MixedDisorder (Ω := Ω) n ξ) (s : RSBScheme k) (h : ℝ)
    (hs : 0 < s.m 1) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (u : ℝ)
    (hu : ∃ σ τ : Config n, overlap n σ τ = u) (d : ℕ) (hd : d ≤ k + 1) :
    (∫ z, mixedGaussianCoupledEvent sk s h t u d z
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      guerraReplicaMeasure n s (mixedBeta ξ) h sk.U t d (overlapEvent n u) :=
  (mixed_integral_gaussianCoupledEvent_eq sk s h hs ⟨ht.1.le, ht.2.le⟩ u hu d hd).trans
    (coupledObservable_eq_replicaMeasure n s (mixedBeta ξ) h sk.U ht d (by omega) (overlapEvent n u))


end FourPapersCommon
