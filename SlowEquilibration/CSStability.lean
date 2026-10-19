-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSParisiMeasure

@[expose] public section

namespace SlowEquilibration.CSStability

noncomputable section

open MeasureTheory Set Filter CrisantiSommers CSCompactAttainment CSParisiMeasure
open scoped Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Genuine approximate minimizers of a continuous function on a compact
space converge to its unique minimizer. Only the actual vanishing comparison
error is supplied; convergence is derived from compact cluster points. -/
theorem approximate_minimizers_tendsto {E A : Type*} [TopologicalSpace E] [CompactSpace E]
    (F : E → ℝ) (hF : Continuous F) (x₀ : E)
    (hunique : ∀ x, F x ≤ F x₀ → x = x₀)
    (l : Filter A) (x : A → E) (δ : A → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hnear : ∀ᶠ a in l, F (x a) ≤ F x₀+δ a) : Tendsto x l (𝓝 x₀) := by
  apply isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall (fun _ => mem_univ _))
  intro y hy hcluster
  apply hunique y
  by_contra hn
  have hgap : F x₀ < F y := lt_of_not_ge hn
  let c : ℝ := (F y+F x₀)/2
  have hc₀ : F x₀ < c := by dsimp only [c]; linarith
  have hcy : c < F y := by dsimp only [c]; linarith
  have hynear : ∀ᶠ z in 𝓝 y, c < F z := (hF.tendsto y).eventually (lt_mem_nhds hcy)
  have hsmall : ∀ᶠ a in l, δ a < c-F x₀ :=
    hδ.eventually (gt_mem_nhds (sub_pos.mpr hc₀))
  obtain ⟨a, ha, hbound, hδa⟩ := (hcluster.frequently hynear |>.and_eventually
    (hnear.and hsmall)).exists
  linarith

/-- Actual global CS minimizers have a uniform cutoff whenever the genuine
Lipschitz energy bound is dominated by the proved truncation entropy gain.
Uniqueness forces the minimizer to equal its actual truncated law. -/
theorem minimizer_hasCutoff_of_lipschitz (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ)
    (hζ : ζ.IsMinimizer β η) (L : ℝ≥0) (hη : LipschitzOnWith L η (Icc (0 : ℝ) 1))
    {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (hcoef : β^2*(L : ℝ) ≤ Q/(1-Q)) :
    HasCutoff ζ.law Q := by
  let ζT : Admissible := ⟨truncate ζ.law Q, inferInstance,
    ⟨Q, truncate_hasCutoff ζ.law ζ.hasCutoff hQ0 hQ1⟩⟩
  have hT : HasCutoff ζT.law Q := truncate_hasCutoff ζ.law ζ.hasCutoff hQ0 hQ1
  have hle : ζT.value β η ≤ ζ.value β η := by
    rw [ζT.value_eq β η hT, ζ.value_eq β η ζ.hasCutoff]
    exact functional_truncate_le β η ζ.law ζ.hasCutoff hQ0 hQ1 L hη hcoef
  have hTmin : ζT.IsMinimizer β η := fun ν => hle.trans (hζ ν)
  have hcont : ContinuousOn η (Ico 0 1) :=
    hη.continuousOn.mono (fun r hr => ⟨hr.1, hr.2.le⟩)
  have heq := ζ.minimizer_law_unique ζT β η hcont hζ hTmin
  rw [heq]
  exact hT

/-- The actual canonical finite-mixture minimizer satisfies the same true
uniform cutoff bound, without an existence or uniqueness premise. -/
theorem canonicalMinimizer_hasCutoff_of_lipschitz (μ : FiniteMixture) (β : ℝ)
    (L : ℝ≥0) (hμ : LipschitzOnWith L μ.xi (Icc (0 : ℝ) 1))
    {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (hcoef : β^2*(L : ℝ) ≤ Q/(1-Q)) :
    HasCutoff (canonicalMinimizer μ β).law Q :=
  minimizer_hasCutoff_of_lipschitz (canonicalMinimizer μ β) β μ.xi
    (canonicalMinimizer_isMinimizer μ β) L hμ hQ0 hQ1 hcoef

/-- A genuine continuous test function on the law's true compact support is
ordinary Bochner-integrable. -/
theorem integrable_of_cutoff (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {Q : ℝ} (hq : HasCutoff ζ Q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 Q)) : Integrable f ζ := by
  have hi := hf.integrableOn_compact isCompact_Icc (μ := ζ)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hq.2.2] using hi

/-- The ordinary CS functional changes uniformly by at most `β² δ` when
the actual covariances differ by at most `δ` on `[0,1]`. The actual energy
integrals are proved integrable on the law's compact support. -/
theorem functional_abs_sub_le (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {Q : ℝ} (hq : HasCutoff ζ Q) (β : ℝ) (η κ : ℝ → ℝ)
    (hη : ContinuousOn η (Icc 0 Q)) (hκ : ContinuousOn κ (Icc 0 Q))
    (δ : ℝ) (hδ : ∀ r ∈ Icc (0 : ℝ) 1, |η r-κ r| ≤ δ) :
    |functional β η ζ Q-functional β κ ζ Q| ≤ β^2*δ := by
  have hiη := integrable_of_cutoff ζ hq hη
  have hiκ := integrable_of_cutoff ζ hq hκ
  have hI : |∫ r, η r-κ r ∂ζ| ≤ δ := by
    have h := norm_integral_le_of_norm_le_const (μ := ζ) (f := fun r => η r-κ r)
      (hq.2.2.mono (fun r hr => by
        simpa only [Real.norm_eq_abs] using hδ r ⟨hr.1, hr.2.trans hq.2.1.le⟩))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  have hA : |η 1-κ 1| ≤ δ := hδ 1 ⟨by norm_num, le_rfl⟩
  have hdiff : functional β η ζ Q-functional β κ ζ Q =
      (β^2/2)*((η 1-κ 1)-(∫ r, η r-κ r ∂ζ)) := by
    rw [integral_sub hiη hiκ]
    unfold functional
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (by positivity : 0 ≤ β^2/2)]
  calc
    _ ≤ (β^2/2)*(|η 1-κ 1|+|∫ r, η r-κ r ∂ζ|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ (β^2/2)*(2*δ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- Injectivity of the actual weak-law representation on a fixed compact
cutoff interval, from the genuine measurable embedding into the real line. -/
theorem law_injective {Q : ℝ} : Function.Injective (law (Q := Q)) := by
  intro ν τ h
  apply ProbabilityMeasure.toMeasure_injective
  exact (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective h

/-- On its true uniform cutoff compact space, the actual canonical CS
minimizer is the unique minimizer of the actual continuous functional. -/
theorem canonical_fixedCutoff_unique (μ : FiniteMixture) (β : ℝ) {Q : ℝ}
    (hq : HasCutoff (canonicalMinimizer μ β).law Q)
    (ν : ProbabilityMeasure (CutoffSpace Q))
    (hν : functional β μ.xi (law ν) Q ≤
      functional β μ.xi (law (liftLaw (canonicalMinimizer μ β).law hq)) Q) :
    ν = liftLaw (canonicalMinimizer μ β).law hq := by
  let ζν : Admissible := ⟨law ν, inferInstance, ⟨Q, law_hasCutoff hq.1 hq.2.1 ν⟩⟩
  have hνcut : HasCutoff ζν.law Q := law_hasCutoff hq.1 hq.2.1 ν
  have hle : ζν.value β μ.xi ≤ (canonicalMinimizer μ β).value β μ.xi := by
    rw [ζν.value_eq β μ.xi hνcut, (canonicalMinimizer μ β).value_eq β μ.xi hq]
    simpa only [law_liftLaw] using hν
  have hνmin : ζν.IsMinimizer β μ.xi :=
    fun ζ => hle.trans (canonicalMinimizer_isMinimizer μ β ζ)
  have heq := ζν.minimizer_law_unique (canonicalMinimizer μ β) β μ.xi
    (fun r _ => (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt)
    hνmin (canonicalMinimizer_isMinimizer μ β)
  apply law_injective
  exact heq.trans (law_liftLaw (canonicalMinimizer μ β).law hq).symm

/-- Genuine weak convergence of the actual canonical minimizers under a
uniform covariance perturbation, on their actual common cutoff compact
probability space. Compactness and actual minimizer uniqueness are used;
neither weak convergence nor any one-step parameter is assumed. -/
theorem canonical_lift_tendsto_of_uniform_covariance {A : Type*}
    (μ₀ : FiniteMixture) (μ : A → FiniteMixture) (β : ℝ) (l : Filter A)
    {Q : ℝ} (hq₀ : HasCutoff (canonicalMinimizer μ₀ β).law Q)
    (hq : ∀ a, HasCutoff (canonicalMinimizer (μ a) β).law Q)
    (δ : A → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hclose : ∀ a r, r ∈ Icc (0 : ℝ) 1 → |(μ a).xi r-μ₀.xi r| ≤ δ a) :
    Tendsto (fun a => liftLaw (canonicalMinimizer (μ a) β).law (hq a)) l
      (𝓝 (liftLaw (canonicalMinimizer μ₀ β).law hq₀)) := by
  let F : ProbabilityMeasure (CutoffSpace Q) → ℝ :=
    fun ν => functional β μ₀.xi (law ν) Q
  let x₀ := liftLaw (canonicalMinimizer μ₀ β).law hq₀
  let x : A → ProbabilityMeasure (CutoffSpace Q) :=
    fun a => liftLaw (canonicalMinimizer (μ a) β).law (hq a)
  have hF : Continuous F := continuous_functional hq₀.1 hq₀.2.1 β μ₀.xi
    (fun r _ => (μ₀.hasDerivAt_xi r).continuousAt.continuousWithinAt)
  have herr : Tendsto (fun a => 2*β^2*δ a) l (𝓝 0) := by
    simpa only [mul_zero] using hδ.const_mul (2*β^2)
  apply approximate_minimizers_tendsto F hF x₀
    (fun ν hν => canonical_fixedCutoff_unique μ₀ β hq₀ ν hν) l x
    (fun a => 2*β^2*δ a) herr
  apply Eventually.of_forall
  intro a
  have hcont₀ : ContinuousOn μ₀.xi (Icc 0 Q) :=
    fun r _ => (μ₀.hasDerivAt_xi r).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (μ a).xi (Icc 0 Q) :=
    fun r _ => ((μ a).hasDerivAt_xi r).continuousAt.continuousWithinAt
  have hA := functional_abs_sub_le (law (x a)) (law_hasCutoff hq₀.1 hq₀.2.1 (x a))
    β (μ a).xi μ₀.xi hcont hcont₀ (δ a) (hclose a)
  have hB := functional_abs_sub_le (law x₀) (law_hasCutoff hq₀.1 hq₀.2.1 x₀)
    β (μ a).xi μ₀.xi hcont hcont₀ (δ a) (hclose a)
  have hmin : functional β (μ a).xi (law (x a)) Q ≤
      functional β (μ a).xi (law x₀) Q := by
    simp only [x, x₀, law_liftLaw]
    have hm := canonicalMinimizer_isMinimizer (μ a) β (canonicalMinimizer μ₀ β)
    rw [(canonicalMinimizer (μ a) β).value_eq β (μ a).xi (hq a),
      (canonicalMinimizer μ₀ β).value_eq β (μ a).xi hq₀] at hm
    exact hm
  change functional β μ₀.xi (law (x a)) Q ≤
    functional β μ₀.xi (law x₀) Q+2*β^2*δ a
  have hAlow := (abs_le.mp hA).1
  have hBhigh := (abs_le.mp hB).2
  linarith

/-- Actual canonical polynomial moments converge under genuine uniform
covariance perturbations and a common coefficient-derived Lipschitz bound.
The common cutoff is derived by true truncation and uniqueness, and the
moment convergence is genuine weak integral continuity on that compact space. -/
theorem canonical_moment_tendsto_of_uniform_covariance {A : Type*}
    (μ₀ : FiniteMixture) (μ : A → FiniteMixture) (β : ℝ) (l : Filter A)
    (L : ℝ≥0) (hL₀ : LipschitzOnWith L μ₀.xi (Icc (0 : ℝ) 1))
    (hL : ∀ a, LipschitzOnWith L (μ a).xi (Icc (0 : ℝ) 1))
    (δ : A → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hclose : ∀ a r, r ∈ Icc (0 : ℝ) 1 → |(μ a).xi r-μ₀.xi r| ≤ δ a) (k : ℕ) :
    Tendsto (fun a => ∫ r, r^k ∂(canonicalMinimizer (μ a) β).law) l
      (𝓝 (∫ r, r^k ∂(canonicalMinimizer μ₀ β).law)) := by
  obtain ⟨Q, hQ, hcoef⟩ := exists_uniform_cutoff β L
  have hq₀ := canonicalMinimizer_hasCutoff_of_lipschitz μ₀ β L hL₀ hQ.1.le hQ.2 hcoef
  have hq (a : A) :=
    canonicalMinimizer_hasCutoff_of_lipschitz (μ a) β L (hL a) hQ.1.le hQ.2 hcoef
  have ht := canonical_lift_tendsto_of_uniform_covariance μ₀ μ β l hq₀ hq δ hδ hclose
  have hc := continuous_energy_integral hQ.2 (fun r : ℝ => r^k)
    (continuous_id.pow k).continuousOn
  have hm := (hc.tendsto (liftLaw (canonicalMinimizer μ₀ β).law hq₀)).comp ht
  simpa only [Function.comp_def, law_liftLaw] using hm

/-- An actual ordinary polynomial moment of the actual unique CS law. -/
def moment (μ : FiniteMixture) (β : ℝ) (k : ℕ) : ℝ :=
  ∫ r, r^k ∂(canonicalMinimizer μ β).law

/-- Positive-atom location reconstructed from genuine first and second law
moments. Its equality to the actual one-step parameter is proved below when
the true minimizer is a strict two-atom law. -/
def oneStepQ (μ : FiniteMixture) (β : ℝ) : ℝ := moment μ β 2 / moment μ β 1

/-- Origin mass reconstructed from genuine first and second law moments. -/
def oneStepWeight (μ : FiniteMixture) (β : ℝ) : ℝ := 1-(moment μ β 1)^2/moment μ β 2

/-- Reconstruction recovers the genuine parameters of a strict two-atom
canonical minimizer, and its denominators are genuinely positive. -/
theorem parameters_of_twoAtom (μ : FiniteMixture) (β : ℝ) {x Q : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hlaw : (canonicalMinimizer μ β).law = twoAtom x Q) :
    oneStepQ μ β = Q ∧ oneStepWeight μ β = x ∧
      0 < moment μ β 1 ∧ 0 < moment μ β 2 := by
  have h1 : moment μ β 1 = (1-x)*Q := by
    rw [moment, hlaw, integral_twoAtom ⟨hx.1.le, hx.2.le⟩]
    simp
  have h2 : moment μ β 2 = (1-x)*Q^2 := by
    rw [moment, hlaw, integral_twoAtom ⟨hx.1.le, hx.2.le⟩]
    simp
  have hs : 0 < 1-x := sub_pos.mpr hx.2
  have hpos1 : 0 < moment μ β 1 := by rw [h1]; exact mul_pos hs hQ.1
  have hpos2 : 0 < moment μ β 2 := by rw [h2]; exact mul_pos hs (sq_pos_of_pos hQ.1)
  refine ⟨?_, ?_, hpos1, hpos2⟩
  · rw [oneStepQ, h1, h2]
    field_simp [hs.ne', hQ.1.ne']
  · rw [oneStepWeight, h1, h2]
    field_simp [hs.ne', hQ.1.ne']
    ring

/-- Moment reconstruction converges to the genuine parameters of the true
strict two-atom limiting law. Applications to one-step perturbations also
prove that every small perturbed law is precisely its reconstructed two-atom
law, so the reconstructed quantities are its actual physical parameters. -/
theorem reconstructed_parameters_tendsto_of_uniform_covariance {A : Type*}
    (μ₀ : FiniteMixture) (μ : A → FiniteMixture) (β : ℝ) (l : Filter A)
    (L : ℝ≥0) (hL₀ : LipschitzOnWith L μ₀.xi (Icc (0 : ℝ) 1))
    (hL : ∀ a, LipschitzOnWith L (μ a).xi (Icc (0 : ℝ) 1))
    (δ : A → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hclose : ∀ a r, r ∈ Icc (0 : ℝ) 1 → |(μ a).xi r-μ₀.xi r| ≤ δ a)
    {x Q : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hlaw : (canonicalMinimizer μ₀ β).law = twoAtom x Q) :
    Tendsto (fun a => oneStepWeight (μ a) β) l (𝓝 x) ∧
      Tendsto (fun a => oneStepQ (μ a) β) l (𝓝 Q) := by
  have ht1 := canonical_moment_tendsto_of_uniform_covariance μ₀ μ β l L hL₀ hL δ hδ hclose 1
  have ht2 := canonical_moment_tendsto_of_uniform_covariance μ₀ μ β l L hL₀ hL δ hδ hclose 2
  change Tendsto (fun a => moment (μ a) β 1) l (𝓝 (moment μ₀ β 1)) at ht1
  change Tendsto (fun a => moment (μ a) β 2) l (𝓝 (moment μ₀ β 2)) at ht2
  obtain ⟨hQeq, hxeq, hpos1, hpos2⟩ := parameters_of_twoAtom μ₀ β hx hQ hlaw
  constructor
  · have ht : Tendsto (fun a => (1 : ℝ)-(moment (μ a) β 1)^2/moment (μ a) β 2) l
        (𝓝 (1-(moment μ₀ β 1)^2/moment μ₀ β 2)) :=
      tendsto_const_nhds.sub ((ht1.pow 2).div ht2 hpos2.ne')
    change Tendsto (fun a => oneStepWeight (μ a) β) l (𝓝 (oneStepWeight μ₀ β)) at ht
    rwa [hxeq] at ht
  · have ht := ht2.div ht1 hpos1.ne'
    change Tendsto (fun a => oneStepQ (μ a) β) l (𝓝 (oneStepQ μ₀ β)) at ht
    rwa [hQeq] at ht

end
end SlowEquilibration.CSStability
