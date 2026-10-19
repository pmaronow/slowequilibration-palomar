-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSStability
public import SlowEquilibration.CSAuxiliaryDiracCertificate

@[expose] public section

/-! # Actual CS minimizer stability for covariances with a linear term

The compact-cutoff argument applies to arbitrary Lipschitz covariances,
including the source transverse mixtures of degrees one and two. Genuine
admissible minimizers and weak moments are used throughout. No spherical
finite-volume pressure formula is asserted.
-/
namespace SlowEquilibration.CSGeneralCovarianceStability
noncomputable section
open MeasureTheory Set Filter CrisantiSommers CSCompactAttainment CSStability
open CSAuxiliaryDiracCertificate
open scoped Topology NNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual globally minimizing ordinary probability law, obtained by
compact attainment and entropy truncation for the literal covariance. -/
def lipschitzMinimizer (β : ℝ) (η : ℝ → ℝ) (L : ℝ≥0)
    (hη : LipschitzOnWith L η (Icc (0 : ℝ) 1)) : Admissible :=
  Classical.choose (exists_minimizer_of_lipschitz β η L hη)

theorem lipschitzMinimizer_isMinimizer (β : ℝ) (η : ℝ → ℝ) (L : ℝ≥0)
    (hη : LipschitzOnWith L η (Icc (0 : ℝ) 1)) :
    (lipschitzMinimizer β η L hη).IsMinimizer β η :=
  Classical.choose_spec (exists_minimizer_of_lipschitz β η L hη)

/-- Uniqueness of the actual minimizer on its compact cutoff space follows
from the proved strict convexity of the ordinary CS functional. -/
theorem fixedCutoff_unique (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ)
    (hη : ContinuousOn η (Ico (0 : ℝ) 1)) (hmin : ζ.IsMinimizer β η)
    {Q : ℝ} (hq : HasCutoff ζ.law Q) (ν : ProbabilityMeasure (CutoffSpace Q))
    (hν : functional β η (law ν) Q ≤
      functional β η (law (liftLaw ζ.law hq)) Q) :
    ν=liftLaw ζ.law hq := by
  let ζν : Admissible := ⟨law ν,inferInstance,⟨Q,law_hasCutoff hq.1 hq.2.1 ν⟩⟩
  have hνcut : HasCutoff ζν.law Q := law_hasCutoff hq.1 hq.2.1 ν
  have hle : ζν.value β η ≤ ζ.value β η := by
    rw [ζν.value_eq β η hνcut,ζ.value_eq β η hq]
    simpa only [law_liftLaw] using hν
  have hνmin : ζν.IsMinimizer β η := fun τ => hle.trans (hmin τ)
  have heq := ζν.minimizer_law_unique ζ β η hη hνmin hmin
  apply law_injective
  exact heq.trans (law_liftLaw ζ.law hq).symm

/-- Uniform covariance closeness forces genuine weak convergence of
actual globally minimizing laws. Their common compact support is derived
from the common Lipschitz bound, not assumed as a support conclusion. -/
theorem minimizer_moment_tendsto_of_uniform_covariance {A : Type*}
    (β : ℝ) (η₀ : ℝ → ℝ) (η : A → ℝ → ℝ) (ζ₀ : Admissible) (ζ : A → Admissible)
    (hmin₀ : ζ₀.IsMinimizer β η₀) (hmin : ∀ a, (ζ a).IsMinimizer β (η a))
    (l : Filter A) (L : ℝ≥0)
    (hL₀ : LipschitzOnWith L η₀ (Icc (0 : ℝ) 1))
    (hL : ∀ a, LipschitzOnWith L (η a) (Icc (0 : ℝ) 1))
    (δ : A → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hclose : ∀ a r, r ∈ Icc (0 : ℝ) 1 → |η a r-η₀ r| ≤ δ a) (k : ℕ) :
    Tendsto (fun a => ∫ r, r^k ∂(ζ a).law) l
      (𝓝 (∫ r, r^k ∂ζ₀.law)) := by
  obtain ⟨Q,hQ,hcoef⟩ := exists_uniform_cutoff β L
  have hq₀ := minimizer_hasCutoff_of_lipschitz ζ₀ β η₀ hmin₀ L hL₀ hQ.1.le hQ.2 hcoef
  have hq (a : A) := minimizer_hasCutoff_of_lipschitz (ζ a) β (η a) (hmin a)
    L (hL a) hQ.1.le hQ.2 hcoef
  have hcont₀ : ContinuousOn η₀ (Ico (0 : ℝ) 1) :=
    hL₀.continuousOn.mono (fun r hr => ⟨hr.1,hr.2.le⟩)
  have hcont (a : A) : ContinuousOn (η a) (Ico (0 : ℝ) 1) :=
    (hL a).continuousOn.mono (fun r hr => ⟨hr.1,hr.2.le⟩)
  let F : ProbabilityMeasure (CutoffSpace Q) → ℝ := fun ν => functional β η₀ (law ν) Q
  let x₀ := liftLaw ζ₀.law hq₀
  let x : A → ProbabilityMeasure (CutoffSpace Q) := fun a => liftLaw (ζ a).law (hq a)
  have hF : Continuous F := continuous_functional hQ.1.le hQ.2 β η₀ hcont₀
  have herr : Tendsto (fun a => 2*β^2*δ a) l (𝓝 0) := by
    simpa only [mul_zero] using hδ.const_mul (2*β^2)
  have hnear : ∀ᶠ a in l, F (x a) ≤ F x₀+2*β^2*δ a := by
    apply Eventually.of_forall
    intro a
    have hA := functional_abs_sub_le (law (x a))
      (law_hasCutoff hQ.1.le hQ.2 (x a)) β (η a) η₀
      ((hcont a).mono (fun r hr => ⟨hr.1,hr.2.trans_lt hQ.2⟩))
      (hcont₀.mono (fun r hr => ⟨hr.1,hr.2.trans_lt hQ.2⟩)) (δ a) (hclose a)
    have hB := functional_abs_sub_le (law x₀)
      (law_hasCutoff hQ.1.le hQ.2 x₀) β (η a) η₀
      ((hcont a).mono (fun r hr => ⟨hr.1,hr.2.trans_lt hQ.2⟩))
      (hcont₀.mono (fun r hr => ⟨hr.1,hr.2.trans_lt hQ.2⟩)) (δ a) (hclose a)
    have hminimal : functional β (η a) (law (x a)) Q ≤
        functional β (η a) (law x₀) Q := by
      simp only [x,x₀,law_liftLaw]
      have hm := hmin a ζ₀
      rw [(ζ a).value_eq β (η a) (hq a),ζ₀.value_eq β (η a) hq₀] at hm
      exact hm
    change functional β η₀ (law (x a)) Q ≤ functional β η₀ (law x₀) Q+2*β^2*δ a
    linarith [(abs_le.mp hA).1,(abs_le.mp hB).2]
  have ht := approximate_minimizers_tendsto F hF x₀
    (fun ν hν => fixedCutoff_unique ζ₀ β η₀ hcont₀ hmin₀ hq₀ ν hν) l x
    (fun a => 2*β^2*δ a) herr hnear
  have hc := continuous_energy_integral hQ.2 (fun r : ℝ => r^k)
    (continuous_id.pow k).continuousOn
  have hm := (hc.tendsto x₀).comp ht
  simpa only [Function.comp_def,x,x₀,law_liftLaw] using hm

/-- Actual selected minimizers exist and obey the moment limit for any
common-Lipschitz covariance family, including polynomial degree one. -/
theorem lipschitzMinimizer_moment_tendsto {A : Type*}
    (β : ℝ) (η₀ : ℝ → ℝ) (η : A → ℝ → ℝ) (l : Filter A) (L : ℝ≥0)
    (hL₀ : LipschitzOnWith L η₀ (Icc (0 : ℝ) 1))
    (hL : ∀ a, LipschitzOnWith L (η a) (Icc (0 : ℝ) 1))
    (δ : A → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hclose : ∀ a r, r ∈ Icc (0 : ℝ) 1 → |η a r-η₀ r| ≤ δ a) (k : ℕ) :
    Tendsto (fun a => ∫ r, r^k ∂(lipschitzMinimizer β (η a) L (hL a)).law) l
      (𝓝 (∫ r, r^k ∂(lipschitzMinimizer β η₀ L hL₀).law)) :=
  minimizer_moment_tendsto_of_uniform_covariance β η₀ η _ _
    (lipschitzMinimizer_isMinimizer β η₀ L hL₀)
    (fun a => lipschitzMinimizer_isMinimizer β (η a) L (hL a)) l L hL₀ hL δ hδ hclose k

/-- Uniform perturbations of the actual source auxiliary covariance have
moments converging to the source transverse atom. The actual atom is
identified by the proved global Dirac certificate; no minimizer shape or
uniqueness premise is supplied here. -/
theorem auxiliary_lipschitzMinimizer_moment_tendsto {A : Type*}
    (μ : FiniteMixture) {β : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (η : A → ℝ → ℝ) (l : Filter A) (L : ℝ≥0)
    (hL₀ : LipschitzOnWith L (μ.auxiliaryCovariance (Thresholds.qStar μ.xi β))
      (Icc (0 : ℝ) 1))
    (hL : ∀ a, LipschitzOnWith L (η a) (Icc (0 : ℝ) 1))
    (δ : A → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hclose : ∀ a r, r ∈ Icc (0 : ℝ) 1 →
      |η a r-μ.auxiliaryCovariance (Thresholds.qStar μ.xi β) r| ≤ δ a) (k : ℕ) :
    Tendsto (fun a => ∫ r, r^k ∂(lipschitzMinimizer β (η a) L (hL a)).law) l
      (𝓝 ((latitudeDiracLocation (Thresholds.qStar μ.xi β))^k)) := by
  let q := Thresholds.qStar μ.xi β
  have hq : q ∈ Ico (0 : ℝ) 1 :=
    ⟨(μ.qStar_solves_plateau hβ).1.1.le,(μ.qStar_solves_plateau hβ).1.2⟩
  let ζ₀ := latitudeDiracCandidate q hq
  have hmin₀ : ζ₀.IsMinimizer β (μ.auxiliaryCovariance q) :=
    latitudeDiracCandidate_isMinimizer μ hβ
  have ht := minimizer_moment_tendsto_of_uniform_covariance β (μ.auxiliaryCovariance q)
    η ζ₀ (fun a => lipschitzMinimizer β (η a) L (hL a)) hmin₀
    (fun a => lipschitzMinimizer_isMinimizer β (η a) L (hL a)) l L hL₀ hL δ hδ hclose k
  have he : (∫ r, r^k ∂ζ₀.law)=(latitudeDiracLocation q)^k := by
    change (∫ r, r^k ∂Measure.dirac (latitudeDiracLocation q))=_
    simp
  rwa [he] at ht

/-- Exact source amplitude shift of the actual ordinary CS functional.
It holds for every genuine admissible law and every transverse degree,
including degrees one and two. -/
theorem functional_amplitude_shift (β c : ℝ) (η : ℝ → ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ] {Q : ℝ}
    (hζ : HasCutoff ζ Q) (hη : ContinuousOn η (Icc (0 : ℝ) Q)) (k : ℕ) :
    functional β (fun t => η t+c*t^k) ζ Q=
      functional β η ζ Q+(β^2/2)*c*(1-∫ t, t^k ∂ζ) := by
  have hiη := integrable_of_cutoff ζ hζ hη
  have hit : Integrable (fun t : ℝ => t^k) ζ :=
    integrable_of_cutoff ζ hζ (continuous_id.pow k).continuousOn
  unfold functional
  rw [integral_add hiη (hit.const_mul c),integral_const_mul]
  simp only [one_pow,mul_one]
  ring

end
end SlowEquilibration.CSGeneralCovarianceStability
