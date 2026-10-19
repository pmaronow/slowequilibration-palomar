-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSPerturbative
public import SlowEquilibration.CSPureModels
public import SlowEquilibration.CSStability

@[expose] public section

namespace SlowEquilibration.CSPerturbative

open MeasureTheory Set Filter CrisantiSommers CSParisiMeasure CSCompactAttainment CSStability
open scoped Topology NNReal BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace EvenPerturbation

variable {d P : ℕ} (b : EvenPerturbation d P)

/-- The normalized perturbing polynomial lies genuinely between zero and
one on the entire physical overlap interval. -/
theorem polynomial_mem_Icc {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (∑ p ∈ b.coeff.support, b.coeff p*r^p) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Finset.sum_nonneg (fun p _ => mul_nonneg (b.nonneg p) (pow_nonneg hr.1 p)), ?_⟩
  have ht := b.total_le_one
  change (∑ p ∈ b.coeff.support, b.coeff p) ≤ 1 at ht
  calc
    _ ≤ ∑ p ∈ b.coeff.support, b.coeff p := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (pow_le_one₀ hr.1 hr.2) (b.nonneg p)
    _ ≤ 1 := ht

/-- True coefficient normalization gives the uniform covariance error
bound `ε`, independently of the chosen allowed perturbing coefficients. -/
theorem covariance_abs_sub_pure_le (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    |(b.covariance hd ε hε).xi r-(FiniteMixture.pure d (by omega) 1 (by positivity)).xi r| ≤ ε := by
  rw [b.covariance_xi, FiniteMixture.pure_xi, one_mul, add_sub_cancel_left,
    abs_of_nonneg (mul_nonneg hε (b.polynomial_mem_Icc hr).1)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (b.polynomial_mem_Icc hr).2 hε

/-- The actual normalized perturbing coefficient first degree moment is
bounded by its true finite maximum degree. -/
theorem coefficient_degree_moment_le :
    (∑ p ∈ b.coeff.support, b.coeff p*(p : ℝ)) ≤ P := by
  have ht := b.total_le_one
  change (∑ p ∈ b.coeff.support, b.coeff p) ≤ 1 at ht
  calc
    _ ≤ ∑ p ∈ b.coeff.support, b.coeff p*(P : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP : p ≤ P := by
        by_contra hn
        exact (Finsupp.mem_support_iff.mp hp) (b.zero_of_gt p (lt_of_not_ge hn))
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpP) (b.nonneg p)
    _ = (∑ p ∈ b.coeff.support, b.coeff p)*(P : ℝ) := by rw [Finset.sum_mul]
    _ ≤ 1*(P : ℝ) := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg P)
    _ = (P : ℝ) := one_mul _

/-- The true Lipschitz constant of every allowed small perturbed covariance
is at most `2P`; this is derived from its actual finite coefficients. -/
theorem covariance_mixtureLipschitzConstant_le (hd : 3 ≤ d) (hdP : d ≤ P)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    mixtureLipschitzConstant (b.covariance hd ε hε) ≤ 2*(P : ℝ≥0) := by
  apply NNReal.coe_le_coe.mp
  change (Finsupp.single d 1+ε • b.coeff).sum (fun p c => c*(p : ℝ)) ≤ 2*(P : ℝ)
  rw [Finsupp.sum_add_index' (by intro p; simp) (by intro p a c; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_smul_index (by intro p; simp)]
  simp only [one_mul, Finsupp.sum]
  have hw : (∑ p ∈ b.coeff.support, (ε*b.coeff p)*(p : ℝ)) =
      ε*(∑ p ∈ b.coeff.support, b.coeff p*(p : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hw]
  have hdP' : (d : ℝ) ≤ P := by exact_mod_cast hdP
  have hsnonneg : 0 ≤ ∑ p ∈ b.coeff.support, b.coeff p*(p : ℝ) :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (b.nonneg p) (Nat.cast_nonneg p))
  have hmul := mul_le_mul hε1 b.coefficient_degree_moment_le hsnonneg (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

/-- A genuine uniform Lipschitz estimate for every allowed perturbation,
including zero coefficients and zero perturbation amplitude. -/
theorem covariance_lipschitzOn (hd : 3 ≤ d) (hdP : d ≤ P)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    LipschitzOnWith (2*(P : ℝ≥0)) (b.covariance hd ε hε).xi (Icc (0 : ℝ) 1) :=
  (mixture_xi_lipschitzOn (b.covariance hd ε hε)).weaken
    (b.covariance_mixtureLipschitzConstant_le hd hdP hε hε1)

end EvenPerturbation

variable {d P : ℕ}

/-- The genuine pure covariance has the same common Lipschitz bound used
for all its normalized perturbations. -/
theorem pure_lipschitzOn (hd : 3 ≤ d) (hdP : d ≤ P) :
    LipschitzOnWith (2*(P : ℝ≥0))
      (FiniteMixture.pure d (by omega) 1 (by positivity)).xi (Icc (0 : ℝ) 1) := by
  apply (mixture_xi_lipschitzOn (FiniteMixture.pure d (by omega) 1 (by positivity))).weaken
  apply NNReal.coe_le_coe.mp
  change (∑ p ∈ (FiniteMixture.pure d (by omega) 1 (by positivity)).coeff.support,
    (FiniteMixture.pure d (by omega) 1 (by positivity)).coeff p*(p : ℝ)) ≤ 2*(P : ℝ)
  rw [CSPureModels.pure_support]
  simp only [Finset.sum_singleton, FiniteMixture.pure, Finsupp.single_eq_same, one_mul]
  have h : (d : ℝ) ≤ P := by exact_mod_cast hdP
  linarith [Nat.cast_nonneg (α := ℝ) P]

/-- Uniform sequential stability across arbitrary allowed perturbing
coefficient families. The only perturbation-size input is the genuine
amplitude tending to zero; actual minimizer weak convergence and moment
reconstruction supply both limiting parameters. -/
theorem covariance_parameters_tendsto (hd : 3 ≤ d) (hdP : d ≤ P) (β : ℝ)
    (hβ : Thresholds.staticThreshold
      (FiniteMixture.pure d (by omega) 1 (by positivity)).xi < β)
    (b : ℕ → EvenPerturbation d P) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hεt : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => oneStepWeight ((b n).covariance hd (ε n) (hε n)) β) atTop
      (𝓝 (oneStepWeight (FiniteMixture.pure d (by omega) 1 (by positivity)) β)) ∧
    Tendsto (fun n => oneStepQ ((b n).covariance hd (ε n) (hε n)) β) atTop
      (𝓝 (oneStepQ (FiniteMixture.pure d (by omega) 1 (by positivity)) β)) := by
  obtain ⟨x, hx, Q, hQ, hlaw, hrest⟩ :=
    CSPureModels.pure_canonicalMinimizer_strict_oneStep d hd 1 (by positivity) hβ
  have hp := parameters_of_twoAtom (FiniteMixture.pure d (by omega) 1 (by positivity)) β hx hQ hlaw
  have ht := reconstructed_parameters_tendsto_of_uniform_covariance
    (FiniteMixture.pure d (by omega) 1 (by positivity))
    (fun n => (b n).covariance hd (ε n) (hε n)) β atTop (2*(P : ℝ≥0))
    (pure_lipschitzOn hd hdP)
    (fun n => (b n).covariance_lipschitzOn hd hdP (hε n) (hε1 n))
    ε hεt (fun n r hr => (b n).covariance_abs_sub_pure_le hd (ε n) (hε n) hr) hx hQ hlaw
  rwa [← hp.2.1, ← hp.1] at ht

/-- For every genuinely small even perturbation, the quantities reconstructed
from moments are exactly the actual parameters of its actual strict
one-step canonical law. This proves that the stability limits refer to
physical one-step parameters rather than a surrogate parameterization. -/
theorem covariance_parameters_are_oneStep (hd : 4 ≤ d) (hdEven : Even d)
    (b : EvenPerturbation d P) (β : ℝ)
    (hβ : Thresholds.staticThreshold
      (FiniteMixture.pure d (by omega) 1 (by positivity)).xi < β)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε < EvenPerturbation.epsilonBound P) :
    oneStepWeight (b.covariance (by omega) ε hε) β ∈ Ioo (0 : ℝ) 1 ∧
    oneStepQ (b.covariance (by omega) ε hε) β ∈ Ioo (0 : ℝ) 1 ∧
    (canonicalMinimizer (b.covariance (by omega) ε hε) β).law =
      twoAtom (oneStepWeight (b.covariance (by omega) ε hε) β)
        (oneStepQ (b.covariance (by omega) ε hε) β) := by
  obtain ⟨hparity, x, hx, Q, hQ, hlaw, hrest⟩ :=
    b.small_even_perturbation_strict_oneStep hd hdEven hε hsmall hβ
  have hp := parameters_of_twoAtom (b.covariance (by omega) ε hε) β hx hQ hlaw
  rw [hp.1, hp.2.1]
  exact ⟨hx, hQ, hlaw⟩

/-- Genuine uniform convergence of both canonical one-step parameters over
all allowed normalized coefficient families. The radius depends on the
base model, degree cutoff, inverse temperature, and tolerance, and is
independent of the perturbing coefficients. -/
theorem covariance_parameters_uniform (hd : 3 ≤ d) (hdP : d ≤ P) (β : ℝ)
    (hβ : Thresholds.staticThreshold
      (FiniteMixture.pure d (by omega) 1 (by positivity)).xi < β)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (b : EvenPerturbation d P) (ε : ℝ) (hε : 0 ≤ ε),
      ε ≤ 1 → ε < δ →
        |oneStepWeight (b.covariance hd ε hε) β-
          oneStepWeight (FiniteMixture.pure d (by omega) 1 (by positivity)) β| < τ ∧
        |oneStepQ (b.covariance hd ε hε) β-
          oneStepQ (FiniteMixture.pure d (by omega) 1 (by positivity)) β| < τ := by
  classical
  by_contra hn
  have hfail (δ : ℝ) (hδ : 0 < δ) :
      ∃ b : EvenPerturbation d P, ∃ ε : ℝ, ∃ hε : 0 ≤ ε,
        ε ≤ 1 ∧ ε < δ ∧ ¬(
          |oneStepWeight (b.covariance hd ε hε) β-
            oneStepWeight (FiniteMixture.pure d (by omega) 1 (by positivity)) β| < τ ∧
          |oneStepQ (b.covariance hd ε hε) β-
            oneStepQ (FiniteMixture.pure d (by omega) 1 (by positivity)) β| < τ) := by
    by_contra hh
    apply hn
    refine ⟨δ, hδ, ?_⟩
    intro b ε hε hε1 hεδ
    by_contra hbad
    exact hh ⟨b, ε, hε, hε1, hεδ, hbad⟩
  have hpos (n : ℕ) : 0 < 1/((n : ℝ)+1) := by positivity
  choose b ε hε hε1 hsmall hbad using fun n : ℕ => hfail (1/((n : ℝ)+1)) (hpos n)
  have ht : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero hε (fun n => (hsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨hx, hQ⟩ := covariance_parameters_tendsto hd hdP β hβ b ε hε hε1 ht
  have hx₀ : Tendsto (fun n => |oneStepWeight ((b n).covariance hd (ε n) (hε n)) β-
      oneStepWeight (FiniteMixture.pure d (by omega) 1 (by positivity)) β|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (hx.sub_const (oneStepWeight (FiniteMixture.pure d (by omega) 1 (by positivity)) β)).abs
  have hQ₀ : Tendsto (fun n => |oneStepQ ((b n).covariance hd (ε n) (hε n)) β-
      oneStepQ (FiniteMixture.pure d (by omega) 1 (by positivity)) β|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (hQ.sub_const (oneStepQ (FiniteMixture.pure d (by omega) 1 (by positivity)) β)).abs
  obtain ⟨n, hn⟩ := ((hx₀.eventually (gt_mem_nhds hτ)).and
    (hQ₀.eventually (gt_mem_nhds hτ))).exists
  exact hbad n hn

/-- Actual strict one-step parameter convergence in the manuscript's even
finite-perturbation class. One common small radius guarantees actual strict
two-atom laws and the stated parameter tolerance for every allowed
coefficient family; no existence, classification, or stability premise is
assumed. -/
theorem small_even_perturbation_parameters_uniform (hd : 4 ≤ d) (hdEven : Even d)
    (hdP : d ≤ P) (β : ℝ)
    (hβ : Thresholds.staticThreshold
      (FiniteMixture.pure d (by omega) 1 (by positivity)).xi < β)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, δ ∈ Ioo (0 : ℝ) (EvenPerturbation.epsilonBound P) ∧
      ∀ (b : EvenPerturbation d P) (ε : ℝ) (hε : 0 ≤ ε), ε < δ →
        oneStepWeight (b.covariance (by omega) ε hε) β ∈ Ioo (0 : ℝ) 1 ∧
        oneStepQ (b.covariance (by omega) ε hε) β ∈ Ioo (0 : ℝ) 1 ∧
        (canonicalMinimizer (b.covariance (by omega) ε hε) β).law =
          twoAtom (oneStepWeight (b.covariance (by omega) ε hε) β)
            (oneStepQ (b.covariance (by omega) ε hε) β) ∧
        |oneStepWeight (b.covariance (by omega) ε hε) β-
          oneStepWeight (FiniteMixture.pure d (by omega) 1 (by positivity)) β| < τ ∧
        |oneStepQ (b.covariance (by omega) ε hε) β-
          oneStepQ (FiniteMixture.pure d (by omega) 1 (by positivity)) β| < τ := by
  obtain ⟨δ₀, hδ₀, hclose⟩ := covariance_parameters_uniform (by omega) hdP β hβ hτ
  have hEB := EvenPerturbation.epsilonBound_pos (P := P)
  let δ := min δ₀ (min 1 (EvenPerturbation.epsilonBound P/2))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (by norm_num)
    (by positivity : 0 < EvenPerturbation.epsilonBound P/2))
  have hδsmall : δ < EvenPerturbation.epsilonBound P := by
    calc
      δ ≤ min 1 (EvenPerturbation.epsilonBound P/2) := min_le_right _ _
      _ ≤ EvenPerturbation.epsilonBound P/2 := min_le_right _ _
      _ < EvenPerturbation.epsilonBound P := by linarith
  refine ⟨δ, ⟨hδ, hδsmall⟩, ?_⟩
  intro b ε hε hεδ
  have hε1 : ε ≤ 1 := hεδ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεsmall : ε < EvenPerturbation.epsilonBound P := hεδ.trans hδsmall
  obtain ⟨hx, hQ, hlaw⟩ := covariance_parameters_are_oneStep hd hdEven b β hβ ε hε hεsmall
  have hc := hclose b ε hε hε1 (hεδ.trans_le (min_le_left _ _))
  exact ⟨hx, hQ, hlaw, hc.1, hc.2⟩

/-- Full manuscript perturbative certificate, including the genuine
nondegenerate contact and strict positivity away from the two contacts,
together with uniform convergence of its actual parameters. -/
theorem small_even_perturbation_certificate_uniform (hd : 4 ≤ d) (hdEven : Even d)
    (hdP : d ≤ P) (β : ℝ)
    (hβ : Thresholds.staticThreshold
      (FiniteMixture.pure d (by omega) 1 (by positivity)).xi < β)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ : ℝ, δ ∈ Ioo (0 : ℝ) (EvenPerturbation.epsilonBound P) ∧
      ∀ (b : EvenPerturbation d P) (ε : ℝ) (hε : 0 ≤ ε), ε < δ →
        ∃ x ∈ Ioo (0 : ℝ) 1, ∃ Q ∈ Ioo (0 : ℝ) 1,
          (canonicalMinimizer (b.covariance (by omega) ε hε) β).law = twoAtom x Q ∧
          CSStructure.potential (b.covariance (by omega) ε hε) β
            (canonicalMinimizer (b.covariance (by omega) ε hε) β).law Q = 0 ∧
          deriv (CSStructure.potential (b.covariance (by omega) ε hε) β
            (canonicalMinimizer (b.covariance (by omega) ε hε) β).law) Q = 0 ∧
          0 < deriv (deriv (CSStructure.potential (b.covariance (by omega) ε hε) β
            (canonicalMinimizer (b.covariance (by omega) ε hε) β).law)) Q ∧
          (∀ r ∈ Ioo (0 : ℝ) 1, r ≠ Q → 0 <
            CSStructure.potential (b.covariance (by omega) ε hε) β
              (canonicalMinimizer (b.covariance (by omega) ε hε) β).law r) ∧
          |x-oneStepWeight (FiniteMixture.pure d (by omega) 1 (by positivity)) β| < τ ∧
          |Q-oneStepQ (FiniteMixture.pure d (by omega) 1 (by positivity)) β| < τ := by
  obtain ⟨δ, hδ, hclose⟩ := small_even_perturbation_parameters_uniform hd hdEven hdP β hβ hτ
  refine ⟨δ, hδ, ?_⟩
  intro b ε hε hεδ
  obtain ⟨hparity, x, hx, Q, hQ, hlaw, hrest⟩ :=
    b.small_even_perturbation_strict_oneStep hd hdEven hε (hεδ.trans hδ.2) hβ
  have hp := parameters_of_twoAtom (b.covariance (by omega) ε hε) β hx hQ hlaw
  obtain ⟨hW, hQ', hlaw', hxclose, hQclose⟩ := hclose b ε hε hεδ
  rw [hp.1] at hQclose
  rw [hp.2.1] at hxclose
  exact ⟨x, hx, Q, hQ, hlaw, hrest.1, hrest.2.1, hrest.2.2.1,
    hrest.2.2.2, hxclose, hQclose⟩

end
end SlowEquilibration.CSPerturbative
