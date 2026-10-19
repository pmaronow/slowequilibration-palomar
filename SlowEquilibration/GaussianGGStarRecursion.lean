-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGFunctional
public import SlowEquilibration.GaussianNegativeStarGeometry

/-! The hard negative-star recurrence is an exact identity of ordinary
replica expectations. Old-neighbor indicator terms equal the original
star observable, while the fresh term is the next star. Its error is the
actual GG indicator discrepancy, subsequently bounded through genuine
continuous and polynomial tests. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGStarRecursion

open MeasureTheory ProbabilityTheory Set
open GaussianNegativeStarGeometry GaussianGGIndicatorTransfer
open GaussianGGCutoffs GaussianGGPolynomialTests
open scoped Topology BigOperators

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The literal hard negative-star indicator under finite replicas. -/
def starObservable (ε : ℝ) (m : ℕ) (σ : Fin (m+1) → H) : ℝ :=
  (negativeStar ε m).indicator (fun _ => (1:ℝ)) σ

def replicaPrefix {m : ℕ} (σ : Fin (m+2) → H) : Fin (m+1) → H :=
  fun j => σ j.castSucc

def prefixStar (ε : ℝ) (m : ℕ) (σ : Fin (m+2) → H) : ℝ :=
  starObservable ε m (replicaPrefix σ)

def freshOverlap (m : ℕ) (σ : Fin (m+2) → H) : ℝ :=
  inner ℝ (σ 0) (σ (Fin.last (m+1)))

def oldOverlap (m : ℕ) (j : Fin m) (σ : Fin (m+2) → H) : ℝ :=
  inner ℝ (σ 0) (σ j.succ.castSucc)

def negativeStep (ε : ℝ) : ℝ → ℝ :=
  (Iic (-ε)).indicator (fun _ => (1:ℝ))

theorem starObservable_mem (ε : ℝ) (m : ℕ) (σ : Fin (m+1) → H) :
    starObservable ε m σ∈Icc (0:ℝ) 1 := by
  classical
  unfold starObservable
  by_cases h : σ∈negativeStar ε m
  · rw [indicator_of_mem h];norm_num
  · rw [indicator_of_notMem h];norm_num

theorem star_mem_iff_prefix_and_fresh (ε : ℝ) (m : ℕ) (σ : Fin (m+2) → H) :
    σ∈negativeStar ε (m+1) ↔
      replicaPrefix σ∈negativeStar ε m ∧ freshOverlap m σ≤-ε := by
  change (∀j : Fin (m+1), inner ℝ (σ 0) (σ j.succ)≤-ε) ↔ _
  rw [Fin.forall_iff_castSucc]
  have hlast : (Fin.last m).succ=Fin.last (m+1) := rfl
  have hsucc (j : Fin m) : j.castSucc.succ=j.succ.castSucc := rfl
  simp only [hlast,hsucc]
  change freshOverlap m σ≤-ε ∧ (∀j : Fin m, oldOverlap m j σ≤-ε) ↔ _
  have hprefix : replicaPrefix σ∈negativeStar ε m ↔ ∀j : Fin m, oldOverlap m j σ≤-ε := by
    rfl
  rw [hprefix]
  exact and_comm

/-- Fresh overlap multiplication appends the literal next negative star. -/
theorem prefixStar_mul_fresh (ε : ℝ) (m : ℕ) (σ : Fin (m+2) → H) :
    prefixStar ε m σ*negativeStep ε (freshOverlap m σ)=starObservable ε (m+1) σ := by
  classical
  have hmem := star_mem_iff_prefix_and_fresh ε m σ
  unfold prefixStar starObservable negativeStep
  by_cases hp : replicaPrefix σ∈negativeStar ε m
  · rw [indicator_of_mem hp,one_mul]
    by_cases hr : freshOverlap m σ≤-ε
    · rw [indicator_of_mem (show freshOverlap m σ∈Iic (-ε) from hr),
        indicator_of_mem (hmem.mpr ⟨hp,hr⟩)]
    · rw [indicator_of_notMem (show freshOverlap m σ∉Iic (-ε) from hr),
        indicator_of_notMem (fun h => hr (hmem.mp h).2)]
  · rw [indicator_of_notMem hp,zero_mul,
      indicator_of_notMem (fun h => hp (hmem.mp h).1)]

/-- Every old-neighbor step is already one on the original hard star. -/
theorem prefixStar_mul_old (ε : ℝ) (m : ℕ) (j : Fin m) (σ : Fin (m+2) → H) :
    prefixStar ε m σ*negativeStep ε (oldOverlap m j σ)=prefixStar ε m σ := by
  classical
  unfold prefixStar starObservable
  by_cases hp : replicaPrefix σ∈negativeStar ε m
  · rw [indicator_of_mem hp,one_mul]
    exact indicator_of_mem (show oldOverlap m j σ∈Iic (-ε) from hp j) _
  · rw [indicator_of_notMem hp,zero_mul]

section Measurable
variable [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

 theorem starObservable_measurable (ε : ℝ) (m : ℕ) :
    Measurable (starObservable (H := H) ε m) :=
  measurable_const.indicator (negativeStar_measurable ε m)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H] [BorelSpace H] in
theorem replicaPrefix_measurable (m : ℕ) : Measurable (replicaPrefix (H := H) (m := m)) :=
  Measurable.of_eval fun j => measurable_pi_apply j.castSucc

 theorem prefixStar_measurable (ε : ℝ) (m : ℕ) :
    Measurable (prefixStar (H := H) ε m) :=
  (starObservable_measurable ε m).comp (replicaPrefix_measurable m)

 theorem freshOverlap_measurable (m : ℕ) : Measurable (freshOverlap (H := H) m) :=
  ((continuous_apply 0).inner (continuous_apply (Fin.last (m+1)))).measurable

 theorem oldOverlap_measurable (m : ℕ) (j : Fin m) : Measurable (oldOverlap (H := H) m j) :=
  ((continuous_apply 0).inner (continuous_apply j.succ.castSucc)).measurable

omit [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
/-- Exact negative-star recurrence from its true indicator GG discrepancy.
The replica law may include an arbitrary ordinary disorder ensemble. -/
theorem discrepancy_star_recursion {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (m : ℕ) (ε : ℝ) (σ : Ω → (Fin (m+2) → H)) :
    discrepancy m μ ρ (fun ω => prefixStar ε m (σ ω))
      (fun ω => freshOverlap m (σ ω)) (fun j ω => oldOverlap m j (σ ω)) (negativeStep ε) =
      (∫ω,starObservable ε (m+1) (σ ω) ∂μ)-
        (((m:ℝ)+ρ.real (Iic (-ε)))/((m:ℝ)+1)) *
          (∫ω,prefixStar ε m (σ ω) ∂μ) := by
  have hFresh : (∫ω,prefixStar ε m (σ ω)*negativeStep ε (freshOverlap m (σ ω)) ∂μ)=
      (∫ω,starObservable ε (m+1) (σ ω) ∂μ) := by
    apply integral_congr_ae
    exact .of_forall fun ω => prefixStar_mul_fresh ε m (σ ω)
  have hOld (j : Fin m) :
      (∫ω,prefixStar ε m (σ ω)*negativeStep ε (oldOverlap m j (σ ω)) ∂μ)=
        (∫ω,prefixStar ε m (σ ω) ∂μ) := by
    apply integral_congr_ae
    exact .of_forall fun ω => prefixStar_mul_old ε m j (σ ω)
  have hStep : (∫r,negativeStep ε r ∂ρ)=ρ.real (Iic (-ε)) := by
    rw [negativeStep,integral_indicator_const 1 measurableSet_Iic,smul_eq_mul,mul_one]
  unfold discrepancy
  rw [hFresh,hStep]
  simp_rw [hOld]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Genuine power-test control yields the hard-star recursion error;
no negative-indicator GG identity is a premise. -/
theorem star_recursion_error_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (m : ℕ) (σ : Ω → (Fin (m+2) → H)) (hσ : Measurable σ)
    (hR : HasLaw (fun ω => freshOverlap m (σ ω)) ρ μ)
    (hQ : ∀j, HasLaw (fun ω => oldOverlap m j (σ ω)) ρ μ)
    (hρ : ∀ᵐ r ∂ρ, r∈Icc (-1:ℝ) 1)
    {ε : ℝ} {M : ℕ} (hε : 0 < ε) (hM : 0 < M) (j : Fin M)
    (P : Polynomial ℝ) {K : ℕ} (hK : P.natDegree ≤ K) {δ : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀r∈Icc (-1:ℝ) 1, |P.eval r-cutoff ε M j r| ≤ δ)
    (d : ℕ → ℝ)
    (hpower : ∀k∈Finset.range (K+1),
      |discrepancy m μ ρ (fun ω => prefixStar (-leftEndpoint ε M j) m (σ ω))
        (fun ω => freshOverlap m (σ ω)) (fun j ω => oldOverlap m j (σ ω))
          (fun r => r^k)| ≤ d k) :
    |(∫ω,starObservable (-leftEndpoint ε M j) (m+1) (σ ω) ∂μ)-
      (((m:ℝ)+ρ.real (Iic (leftEndpoint ε M j)))/((m:ℝ)+1)) *
        (∫ω,prefixStar (-leftEndpoint ε M j) m (σ ω) ∂μ)| ≤
      (∑k∈Finset.range (K+1), |P.coeff k| * d k)+2*δ+2*ρ.real (shell ε M j) := by
  let f : Ω → ℝ := fun ω => prefixStar (-leftEndpoint ε M j) m (σ ω)
  have hf : AEStronglyMeasurable f μ :=
    ((prefixStar_measurable _ m).comp hσ).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂μ, |f ω|≤1 := .of_forall fun ω => by
    have hm := starObservable_mem (-leftEndpoint ε M j) m (replicaPrefix (σ ω))
    change |starObservable (-leftEndpoint ε M j) m (replicaPrefix (σ ω))| ≤ 1
    rw [abs_of_nonneg hm.1]
    exact hm.2
  have ht := indicator_discrepancy_le_power_defects m μ ρ f
    (fun ω => freshOverlap m (σ ω)) (fun j ω => oldOverlap m j (σ ω))
    hf hb hR hQ hρ hε hM j P hK hδ happrox d hpower
  have hs : (Iic (leftEndpoint ε M j)).indicator (fun _ => (1:ℝ))=
      negativeStep (-leftEndpoint ε M j) := by simp only [negativeStep,neg_neg]
  rw [hs] at ht
  change |discrepancy m μ ρ (fun ω => prefixStar (-leftEndpoint ε M j) m (σ ω))
    (fun ω => freshOverlap m (σ ω)) (fun j ω => oldOverlap m j (σ ω))
    (negativeStep (-leftEndpoint ε M j))| ≤ _ at ht
  rw [discrepancy_star_recursion] at ht
  simpa only [neg_neg] using ht

end Measurable
end SlowEquilibration.GaussianGGStarRecursion
