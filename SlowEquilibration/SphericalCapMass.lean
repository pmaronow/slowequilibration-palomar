-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGuerraBound
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! The manuscript's deterministic cap bound, on actual probability measures
supported on the Euclidean sphere. It applies simultaneously to every axis,
including an axis chosen from the disorder. -/

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def cap {N : ℕ} (v : Vector N) (s : ℝ) : Set (Vector N) := {x | s ≤ overlap x v}

def replicaOverlapEvent {N : ℕ} (t : ℝ) : Set (Vector N × Vector N) :=
  {z | t < overlap z.1 z.2}

theorem cap_measurable {N : ℕ} (v : Vector N) (s : ℝ) : MeasurableSet (cap v s) := by
  unfold cap overlap
  exact (isClosed_le continuous_const (by fun_prop)).measurableSet

theorem replicaOverlapEvent_measurable {N : ℕ} (t : ℝ) : MeasurableSet (replicaOverlapEvent (N := N) t) := by
  unfold replicaOverlapEvent overlap
  exact (isOpen_lt continuous_const (by fun_prop)).measurableSet

theorem sphereMeasure_prod_support {N : ℕ} (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖^2 = (N : ℝ)) :
    ∀ᵐ z : Vector N × Vector N ∂μ.prod μ, ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isClosed_eq (continuous_fst.norm.pow 2) continuous_const).measurableSet.inter
      (isClosed_eq (continuous_snd.norm.pow 2) continuous_const).measurableSet)).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hμ] with y hy
  exact ⟨hx, hy⟩

theorem sphereMeasure_id_integrable {N : ℕ} (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖^2 = (N : ℝ)) : Integrable (fun x => x) μ := by
  apply Integrable.of_bound continuous_id.aestronglyMeasurable (Real.sqrt (N : ℝ))
  filter_upwards [hμ] with x hx
  rw [← hx, Real.sqrt_sq (norm_nonneg _)]
  simp only [id_eq, le_refl]

theorem sphereMeasure_overlap_integrable {N : ℕ} (hN : 1 ≤ N)
    (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖^2 = (N : ℝ)) :
    Integrable (fun z : Vector N × Vector N => overlap z.1 z.2) (μ.prod μ) := by
  apply Integrable.of_bound (by unfold overlap; fun_prop) 1
  filter_upwards [sphereMeasure_prod_support μ hμ] with z hz
  rw [Real.norm_eq_abs]
  exact abs_le.mpr (overlap_mem_Icc_of_norm_sq hN z.1 z.2 hz.1 hz.2)

/-- The unnormalized cap barycenter has a positive axial projection fixed
by the actual cap mass. No conditional law is assumed. -/
theorem cap_barycenter_projection {N : ℕ} (hN : 1 ≤ N)
    (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖^2 = (N : ℝ)) (v : Vector N) (s : ℝ) :
    μ.real (cap v s) * (N : ℝ) * s ≤ inner ℝ (∫ x in cap v s, x ∂μ) v := by
  let ρ := μ.restrict (cap v s)
  have hi : Integrable (fun x : Vector N => x) ρ := (sphereMeasure_id_integrable μ hμ).restrict
  have hip : Integrable (fun x : Vector N => inner ℝ x v) ρ := by
    have hh := (innerSL ℝ v).integrable_comp hi
    change Integrable (fun x : Vector N => inner ℝ v x) ρ at hh
    apply hh.congr
    exact .of_forall fun x => (real_inner_comm v x).symm
  have he : (∫ x : Vector N, inner ℝ x v ∂ρ) = inner ℝ (∫ x, x ∂ρ) v := by
    have hh := (innerSL ℝ v).integral_comp_comm hi
    change (∫ x : Vector N, inner ℝ v x ∂ρ) = inner ℝ v (∫ x, x ∂ρ) at hh
    rw [integral_congr_ae (.of_forall fun x => real_inner_comm v x), hh]
    exact (real_inner_comm v _).symm
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hp : ∀ᵐ x ∂ρ, (N : ℝ)*s ≤ inner ℝ x v := by
    filter_upwards [ae_restrict_mem (cap_measurable v s)] with x hx
    have hh : s ≤ inner ℝ x v / (N : ℝ) := hx
    have hh' := (le_div_iff₀ hNr).mp hh
    linarith
  have hh := integral_mono_ae (integrable_const ((N : ℝ)*s)) hip hp
  rw [he] at hh
  simpa only [ρ, integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul, mul_assoc] using hh

/-- The actual cap-pair overlap integral is the squared norm of the
restricted barycenter divided by the physical radius squared. -/
theorem cap_pair_overlap_eq_barycenter {N : ℕ}
    (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖^2 = (N : ℝ)) (v : Vector N) (s : ℝ) :
    (∫ z : Vector N × Vector N in cap v s ×ˢ cap v s, overlap z.1 z.2 ∂μ.prod μ) =
      ‖∫ x in cap v s, x ∂μ‖^2/(N : ℝ) := by
  let ρ := μ.restrict (cap v s)
  have hi : Integrable (fun x : Vector N => x) ρ := (sphereMeasure_id_integrable μ hμ).restrict
  rw [← Measure.prod_restrict]
  change (∫ z : Vector N × Vector N, inner ℝ z.1 z.2/(N : ℝ) ∂ρ.prod ρ) = _
  rw [integral_div]
  have hh := integral_prod_bilin (innerSL ℝ : Vector N →L[ℝ] Vector N →L[ℝ] ℝ) hi hi
  change (∫ z : Vector N × Vector N, inner ℝ z.1 z.2 ∂ρ.prod ρ) =
    inner ℝ (∫ x, x ∂ρ) (∫ y, y ∂ρ) at hh
  rw [real_inner_self_eq_norm_sq] at hh
  exact congrArg (fun t : ℝ => t/(N : ℝ)) hh

theorem cap_pair_overlap_ge {N : ℕ} (hN : 1 ≤ N)
    (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖^2 = (N : ℝ)) (v : Vector N)
    (hv : ‖v‖^2 = (N : ℝ)) {s : ℝ} (hs : 0 ≤ s) :
    (μ.real (cap v s))^2*s^2 ≤
      ∫ z : Vector N × Vector N in cap v s ×ˢ cap v s, overlap z.1 z.2 ∂μ.prod μ := by
  let α := μ.real (cap v s)
  let m := ∫ x in cap v s, x ∂μ
  have hα : 0 ≤ α := ENNReal.toReal_nonneg
  have hp := cap_barycenter_projection hN μ hμ v s
  change α*(N : ℝ)*s ≤ inner ℝ m v at hp
  have hnr : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hleft : (α*(N : ℝ)*s)^2 ≤ (inner ℝ m v)^2 :=
    (sq_le_sq₀ (mul_nonneg (mul_nonneg hα hnr.le) hs)
      ((mul_nonneg (mul_nonneg hα hnr.le) hs).trans hp)).mpr hp
  have hc := abs_real_inner_le_norm m v
  have hright : (inner ℝ m v)^2 ≤ ‖m‖^2*(N : ℝ) := by
    have hh := (sq_le_sq₀ (abs_nonneg (inner ℝ m v)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hc
    simpa only [sq_abs, mul_pow, hv] using hh
  have hm : (α^2*s^2)*(N : ℝ) ≤ ‖m‖^2 := by
    have hh : ((α^2*s^2)*(N : ℝ))*(N : ℝ) ≤ ‖m‖^2*(N : ℝ) := by nlinarith
    exact (mul_le_mul_iff_left₀ hnr).mp hh
  rw [cap_pair_overlap_eq_barycenter μ hμ v s]
  exact (le_div_iff₀ hnr).mpr hm

/-- Lemma pr-cap in squared form, for an ordinary sphere-supported
probability measure and an arbitrary physical axis. -/
theorem cap_mass_sq_le_replica_mass {N : ℕ} (hN : 1 ≤ N)
    (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖^2 = (N : ℝ)) (v : Vector N)
    (hv : ‖v‖^2 = (N : ℝ)) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    (μ.real (cap v s))^2 ≤ (2-s^2)/s^2 * (μ.prod μ).real (replicaOverlapEvent (N := N) (s^2/2)) := by
  let B := cap v s ×ˢ cap v s
  let E := replicaOverlapEvent (N := N) (s^2/2)
  let t := s^2/2
  have hB : MeasurableSet B := (cap_measurable v s).prod (cap_measurable v s)
  have hE : MeasurableSet E := replicaOverlapEvent_measurable t
  have ht0 : 0 ≤ t := div_nonneg (sq_nonneg _) (by norm_num)
  have ht1 : t < 1 := by dsimp [t]; nlinarith [hs.1, hs.2, sq_nonneg (1-s)]
  have hf := (sphereMeasure_overlap_integrable hN μ hμ).indicator hB
  have hg1 : Integrable (B.indicator (fun _ => t)) (μ.prod μ) := (integrable_const t).indicator hB
  have hg2 : Integrable (E.indicator (fun _ => 1-t)) (μ.prod μ) := (integrable_const (1-t)).indicator hE
  have hpt : ∀ᵐ z : Vector N × Vector N ∂μ.prod μ,
      B.indicator (fun z => overlap z.1 z.2) z ≤
        B.indicator (fun _ => t) z + E.indicator (fun _ => 1-t) z := by
    filter_upwards [sphereMeasure_prod_support μ hμ] with z hz
    have hR := (overlap_mem_Icc_of_norm_sq hN z.1 z.2 hz.1 hz.2).2
    by_cases hzB : z ∈ B
    · by_cases hzE : z ∈ E
      · simp only [indicator_of_mem hzB, indicator_of_mem hzE]
        linarith
      · have hnot : overlap z.1 z.2 ≤ t := le_of_not_gt hzE
        simp only [indicator_of_mem hzB, indicator_of_notMem hzE, add_zero]
        exact hnot
    · by_cases hzE : z ∈ E
      · simp only [indicator_of_notMem hzB, indicator_of_mem hzE, zero_add]
        linarith
      · simp only [indicator_of_notMem hzB, indicator_of_notMem hzE, add_zero, le_refl]
  have hi := integral_mono_ae hf (hg1.add hg2) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add hg1 hg2, integral_indicator hB, integral_indicator_const t hB,
    integral_indicator_const (1-t) hE] at hi
  have hlo := cap_pair_overlap_ge hN μ hμ v hv hs.1.le
  have hp : (μ.prod μ).real B = (μ.real (cap v s))^2 := by
    simp only [B, measureReal_prod_prod, pow_two]
  simp only [smul_eq_mul, hp] at hi
  have hsq : 0 < s^2 := sq_pos_of_pos hs.1
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hsq).mpr
  change (μ.real (cap v s))^2*s^2 ≤ ((2-s^2) * (μ.prod μ).real E)
  dsimp only [t] at hi
  nlinarith

/-- Lemma pr-cap, with its literal square-root constant. The bound is uniform
in every axis on the sphere, even when the axis depends on the disorder. -/
theorem cap_mass_le_sqrt_replica_mass {N : ℕ} (hN : 1 ≤ N)
    (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖^2 = (N : ℝ)) (v : Vector N)
    (hv : ‖v‖^2 = (N : ℝ)) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    μ.real (cap v s) ≤
      Real.sqrt ((2-s^2)/s^2 * (μ.prod μ).real (replicaOverlapEvent (N := N) (s^2/2))) :=
  Real.le_sqrt_of_sq_le (cap_mass_sq_le_replica_mass hN μ hμ v hv hs)

/-- The manuscript's cap estimate applied to the actual ordinary Gibbs law. -/
theorem gibbsLaw_cap_mass_le {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (v : Vector N)
    (hv : ‖v‖^2 = (N : ℝ)) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    (gibbsLaw N β H).real (cap v s) ≤
      Real.sqrt ((2-s^2)/s^2 * ((gibbsLaw N β H).prod (gibbsLaw N β H)).real
        (replicaOverlapEvent (N := N) (s^2/2))) := by
  let _ := gibbsLaw_probability hN β hH
  exact cap_mass_le_sqrt_replica_mass hN _ (gibbsLaw_support hN β H) v hv hs

/-- The cap estimate for the actual finite Gaussian mixed spherical field,
with normalization and support derived from its genuine Gibbs density. -/
theorem mixtureGibbsLaw_cap_mass_le {N : ℕ} (hN : 1 ≤ N)
    (ξ : FiniteMixture) (β : ℝ) (J : Disorder N ξ.maxDegree) (v : Vector N)
    (hv : ‖v‖^2 = (N : ℝ)) {s : ℝ} (hs : s ∈ Ioo 0 1) :
    (mixtureGibbsLaw ξ β J).real (cap v s) ≤
      Real.sqrt ((2-s^2)/s^2 * ((mixtureGibbsLaw ξ β J).prod (mixtureGibbsLaw ξ β J)).real
        (replicaOverlapEvent (N := N) (s^2/2))) :=
  gibbsLaw_cap_mass_le hN β (fieldOfMixture_contDiff ξ J).continuous v hv hs

end
end SlowEquilibration.SphericalModel
