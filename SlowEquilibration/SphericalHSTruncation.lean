-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTruncatedSecondMoment

@[expose] public section

/-!
# A genuine Huang--Sellke partition truncation and its second-moment estimate

The truncation keeps centers whose actual partition outside the small-overlap
band is at most a prescribed threshold. This is the integrated-band version
of the Huang--Sellke free-energy typicality event. Its measurability and second
moment estimate are proved, without any moment estimate as a hypothesis.
Planted typicality, which uses the strict RS condition and band interpolation,
is a separate issue and is not asserted here.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def smallOverlap {N : ℕ} (δ : ℝ) : Set (Vector N × Vector N) :=
  {z | |overlap z.1 z.2| < δ}

theorem smallOverlap_measurable {N : ℕ} (δ : ℝ) :
    MeasurableSet (smallOverlap (N := N) δ) := by
  unfold smallOverlap overlap
  exact (isOpen_lt ((continuous_fst.inner continuous_snd).div_const (N : ℝ)).abs continuous_const).measurableSet

/-- The literal partition in a measurable set of pair overlaps, centered at u. -/
def overlapPartition {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (S : Set (Vector N × Vector N)) (J : Disorder N P) (u : Vector N) : ℝ :=
  ∫ v, S.indicator (fun z => Real.exp (β*field c J z.2)) (u,v) ∂sphereLaw N

theorem overlapPartition_jointMeasurable {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    {S : Set (Vector N × Vector N)} (hS : MeasurableSet S) :
    Measurable (fun z : Disorder N P × Vector N => overlapPartition c β S z.1 z.2) := by
  have hf : StronglyMeasurable (fun z : (Disorder N P × Vector N) × Vector N =>
      S.indicator (fun w => Real.exp (β*field c z.1.1 w.2)) (z.1.2,z.2)) := by
    have he : Measurable (fun z : (Disorder N P × Vector N) × Vector N =>
        Real.exp (β*field c z.1.1 z.2)) :=
      (Real.continuous_exp.comp (continuous_const.mul
        ((field_jointContinuous c).comp (continuous_fst.fst.prodMk continuous_snd)))).measurable
    have hi := he.indicator (hS.preimage (measurable_fst.snd.prodMk measurable_snd))
    convert hi.stronglyMeasurable using 1
    funext z
    by_cases hz : (z.1.2,z.2) ∈ S <;> simp [hz]
  exact hf.integral_prod_right'.measurable

theorem overlapPartition_nonneg {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (S : Set (Vector N × Vector N)) (J : Disorder N P) (u : Vector N) :
    0 ≤ overlapPartition c β S J u := by
  apply integral_nonneg
  intro v
  by_cases hv : (u,v) ∈ S <;> simp [hv,Real.exp_nonneg]

theorem overlapPartition_add_compl {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) {S : Set (Vector N × Vector N)}
    (hS : MeasurableSet S) (J : Disorder N P) (u : Vector N) :
    overlapPartition c β S J u+overlapPartition c β Sᶜ J u = partition N β (field c J) := by
  have hs : MeasurableSet {v : Vector N | (u,v) ∈ S} :=
    hS.preimage (measurable_const.prodMk measurable_id)
  have he : (fun v : Vector N => S.indicator (fun z => Real.exp (β*field c J z.2)) (u,v)) =
      {v : Vector N | (u,v) ∈ S}.indicator (fun v => Real.exp (β*field c J v)) := by
    funext v
    by_cases hv : (u,v) ∈ S <;> simp [hv]
  have hec : (fun v : Vector N => Sᶜ.indicator (fun z => Real.exp (β*field c J z.2)) (u,v)) =
      {v : Vector N | (u,v) ∈ S}ᶜ.indicator (fun v => Real.exp (β*field c J v)) := by
    funext v
    by_cases hv : (u,v) ∈ S <;> simp [hv]
  unfold overlapPartition partition
  rw [he,hec,integral_indicator hs,integral_indicator hs.compl]
  exact integral_add_compl hs (partition_integrand_integrable hN β (field_contDiff c J).continuous)

/-- Integrated-band free-energy typicality is an actual disorder--center event. -/
def hsTruncation {N P : ℕ} (c : Degree P → ℝ) (β δ L : ℝ) :
    Set (Disorder N P × Vector N) :=
  {z | overlapPartition c β (smallOverlap δ)ᶜ z.1 z.2 ≤ Real.exp L}

theorem hsTruncation_measurable {N P : ℕ} (c : Degree P → ℝ) (β δ L : ℝ) :
    MeasurableSet (hsTruncation (N := N) c β δ L) :=
  measurableSet_le (overlapPartition_jointMeasurable c β (smallOverlap_measurable δ).compl) measurable_const

/-- The unrestricted two-spin partition in a specified overlap region. -/
def overlapPairPartition {N P : ℕ} (c : Degree P → ℝ) (β : ℝ)
    (S : Set (Vector N × Vector N)) (J : Disorder N P) : ℝ :=
  ∫ z : Vector N × Vector N,
    S.indicator (fun w => Real.exp (β*field c J w.1)*Real.exp (β*field c J w.2)) z
    ∂(sphereLaw N).prod (sphereLaw N)

theorem overlap_pair_prod_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {S : Set (Vector N × Vector N)} (hS : MeasurableSet S) :
    Integrable (fun z : Disorder N P × (Vector N × Vector N) =>
      S.indicator (fun w => Real.exp (β*field c z.1 w.1)*Real.exp (β*field c z.1 w.2)) z.2)
      ((disorderLaw N P).prod ((sphereLaw N).prod (sphereLaw N))) := by
  convert (field_exp_pair_prod_integrable hN c hc β).indicator (hS.preimage measurable_snd) using 1
  funext z
  by_cases hz : z.2 ∈ S <;> simp [hz]

theorem overlapPairPartition_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {S : Set (Vector N × Vector N)} (hS : MeasurableSet S) :
    Integrable (overlapPairPartition c β S) (disorderLaw N P) :=
  (overlap_pair_prod_integrable hN c hc β hS).integral_prod_left

theorem overlapPairPartition_eq_iterated {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) {S : Set (Vector N × Vector N)}
    (hS : MeasurableSet S) (J : Disorder N P) :
    overlapPairPartition c β S J =
      ∫ u, Real.exp (β*field c J u)*overlapPartition c β S J u ∂sphereLaw N := by
  have hi := (partition_integrand_integrable hN β (field_contDiff c J).continuous).mul_prod
    (partition_integrand_integrable hN β (field_contDiff c J).continuous)
  unfold overlapPairPartition
  rw [integral_prod _ (hi.indicator hS)]
  apply integral_congr_ae
  exact .of_forall fun u => by
    unfold overlapPartition
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun v => by
      by_cases hv : (u,v) ∈ S <;> simp [hv]

theorem overlapPartition_exp_mul_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β : ℝ) {S : Set (Vector N × Vector N)}
    (hS : MeasurableSet S) (J : Disorder N P) :
    Integrable (fun u => Real.exp (β*field c J u)*overlapPartition c β S J u) (sphereLaw N) := by
  have hi := (partition_integrand_integrable hN β (field_contDiff c J).continuous).mul_prod
    (partition_integrand_integrable hN β (field_contDiff c J).continuous)
  convert (hi.indicator hS).integral_prod_left using 1
  funext u
  unfold overlapPartition
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun v => by
    by_cases hv : (u,v) ∈ S <;> simp [hv]

/-- The deterministic Huang--Sellke split into small and large overlaps. -/
theorem hsTruncatedPartition_sq_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (β δ L : ℝ) (J : Disorder N P) :
    (truncatedPartition c β (hsTruncation c β δ L) J)^2 ≤
      overlapPairPartition c β (smallOverlap δ) J+Real.exp L*partition N β (field c J) := by
  let T := hsTruncation (N := N) c β δ L
  let Y := truncatedPartition c β T J
  have hT := hsTruncation_measurable (N := N) c β δ L
  have hiZ := partition_integrand_integrable hN β (field_contDiff c J).continuous
  have hiT : Integrable (fun u => T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (J,u)) (sphereLaw N) := by
    convert hiZ.indicator (hT.preimage ((measurable_const (a := J)).prodMk measurable_id)) using 1
    funext u
    by_cases hu : (J,u) ∈ hsTruncation c β δ L <;> simp [T,hu]
  have hiS := overlapPartition_exp_mul_integrable hN c β (smallOverlap_measurable δ) J
  have hineq : (∫ u, T.indicator (fun w => Real.exp (β*field c w.1 w.2)) (J,u)*Y ∂sphereLaw N) ≤
      ∫ u, Real.exp (β*field c J u)*overlapPartition c β (smallOverlap δ) J u+
        Real.exp L*Real.exp (β*field c J u) ∂sphereLaw N := by
    apply integral_mono (hiT.mul_const Y) (hiS.add (hiZ.const_mul _))
    intro u
    dsimp only [Pi.add_apply]
    by_cases hu : (J,u) ∈ T
    · rw [Set.indicator_of_mem hu]
      dsimp only
      have hfar : overlapPartition c β (smallOverlap δ)ᶜ J u ≤ Real.exp L := hu
      have hYZ := truncatedPartition_le_partition hN c β hT J
      have hsplit := overlapPartition_add_compl hN c β (smallOverlap_measurable δ) J u
      have hlow : Y ≤ overlapPartition c β (smallOverlap δ) J u+Real.exp L := by
        dsimp only [Y]
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hlow (Real.exp_pos (β*field c J u)).le]
    · rw [Set.indicator_of_notMem hu,zero_mul]
      exact add_nonneg (mul_nonneg (Real.exp_pos _).le (overlapPartition_nonneg c β (smallOverlap δ) J u)) (by positivity)
  rw [integral_mul_const,integral_add hiS (hiZ.const_mul _),integral_const_mul,
    ← overlapPairPartition_eq_iterated hN c β (smallOverlap_measurable δ) J] at hineq
  simpa only [Y,T,truncatedPartition,partition,pow_two] using hineq

/-- The covariance on a small-overlap pair is quadratically small for every
nonnegative finite mixture with minimum degree two. -/
theorem covariancePolynomial_le_small {P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {δ r : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hr : |r| ≤ δ) : covariancePolynomial c r ≤ covariancePolynomial c 1*δ^2 := by
  unfold covariancePolynomial
  simp only [one_pow,mul_one]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (hc p)
  calc
    r^p.val.val ≤ |r^p.val.val| := le_abs_self _
    _ = |r|^p.val.val := abs_pow _ _
    _ ≤ δ^p.val.val := pow_le_pow_left₀ (abs_nonneg _) hr _
    _ ≤ δ^2 := pow_le_pow_of_le_one hδ hδ1 p.property

/-- The small-overlap contribution to the second moment has an explicit
finite-dimensional annealed upper bound, including odd mixtures. -/
theorem expected_smallOverlapPairPartition_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∫ J, overlapPairPartition c β (smallOverlap δ) J ∂disorderLaw N P) ≤
      Real.exp ((N : ℝ)*β^2*covariancePolynomial c 1*(1+δ^2)) := by
  have hi := overlap_pair_prod_integrable hN c hc β (smallOverlap_measurable δ)
  unfold overlapPairPartition
  rw [integral_integral_swap hi]
  calc
    _ ≤ ∫ _z : Vector N × Vector N,
        Real.exp ((N : ℝ)*β^2*covariancePolynomial c 1*(1+δ^2))
        ∂(sphereLaw N).prod (sphereLaw N) := by
      apply integral_mono_ae hi.integral_prod_right (integrable_const _)
      filter_upwards [sphereLaw_pair_support hN] with z hz
      by_cases hs : z ∈ smallOverlap δ
      · simp only [Set.indicator_of_mem hs]
        have hpair := pair_truncated_exponential_moment hN c hc β z.1 z.2 hz.1 hz.2
          (T := Set.univ) MeasurableSet.univ
        simp only [Set.indicator_univ,Set.mem_univ,and_self,Set.ofPred_true,probReal_univ,mul_one] at hpair
        rw [hpair]
        apply Real.exp_le_exp.mpr
        have hcov := covariancePolynomial_le_small c hc hδ hδ1
          (show |overlap z.1 z.2| ≤ δ from le_of_lt hs)
        have hm := mul_le_mul_of_nonneg_left hcov (show 0 ≤ (N : ℝ)*β^2 by positivity)
        nlinarith
      · simp only [Set.indicator_of_notMem hs,integral_zero]
        exact (Real.exp_pos _).le
    _ = _ := by simp

/-- The genuine HS truncated second-moment estimate. The event is the
explicit measurable integrated-band typicality event above; there is no
second-moment assumption in this theorem. -/
theorem expected_hsTruncatedPartition_sq_le {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β L : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (∫ J, (truncatedPartition c β (hsTruncation c β δ L) J)^2 ∂disorderLaw N P) ≤
      Real.exp ((N : ℝ)*β^2*covariancePolynomial c 1*(1+δ^2))+
        Real.exp (L+(N : ℝ)*β^2*covariancePolynomial c 1/2) := by
  have hiY := truncatedPartition_sq_integrable hN c hc β (hsTruncation_measurable (N := N) c β δ L)
  have hiS := overlapPairPartition_integrable hN c hc β (smallOverlap_measurable δ)
  have hiZ : Integrable (fun J : Disorder N P => partition N β (field c J)) (disorderLaw N P) :=
    (field_exp_prod_integrable hN c hc β).integral_prod_left
  have hle := integral_mono hiY (hiS.add (hiZ.const_mul (Real.exp L)))
    (hsTruncatedPartition_sq_le hN c β δ L)
  dsimp only [Pi.add_apply] at hle
  rw [integral_add hiS (hiZ.const_mul _),integral_const_mul,
    expected_partition hN c hc β] at hle
  have hsmall := expected_smallOverlapPairPartition_le hN c hc β hδ hδ1
  rw [Real.exp_add]
  exact hle.trans (add_le_add hsmall le_rfl)

end SlowEquilibration.SphericalModel
