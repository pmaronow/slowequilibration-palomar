-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalNestedLatitudeRegularity
public import SlowEquilibration.SphericalLatitudeLaplaceAsymptotics
public import SlowEquilibration.SphericalLinearLower

/-! Fixed positive latitude windows with controlled geometric entropy and
actual partition comparisons, used for deterministic band thickening. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalNestedLatitude
open MeasureTheory Set Filter Metric
open SphericalModel
open scoped Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma partitionAgainst_latitude_eq {n : ℕ} (β : ℝ) {H : Vector (n+1) → ℝ}
    (hH : Continuous H) (u : Vector (n+1)) (q : ℝ) :
    partitionAgainst (latitudeLaw u (latitudeFrameAt u) q) β H=
      partition n β (fun x => H (latitudeMap u (latitudeFrameAt u) q x)) := by
  unfold partitionAgainst latitudeLaw partition
  exact integral_map (latitudeMap_continuous _ _ _).measurable.aemeasurable
    (Real.continuous_exp.comp (continuous_const.mul hH)).aestronglyMeasurable

lemma logPartition_lower_of_pointwise {n : ℕ} (hn : 1 ≤ n) (β : ℝ)
    {H G : Vector n → ℝ} (hH : Continuous H) (hG : Continuous G) {D : ℝ}
    (hle : ∀ z,‖z‖^2=(n:ℝ) → β*H z ≤ β*G z+D) :
    Real.log (partition n β H)-D ≤ Real.log (partition n β G) := by
  have hpart : partition n β H ≤ Real.exp D*partition n β G := by
    unfold partition
    rw [← integral_const_mul]
    apply integral_mono_ae (partition_integrand_integrable hn β hH)
      ((partition_integrand_integrable hn β hG).const_mul _)
    filter_upwards [sphereLaw_support hn] with z hz
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hle z hz])
  have hh := Real.log_le_log (partition_pos hn β hH) hpart
  rw [Real.log_mul (Real.exp_ne_zero D) (partition_pos hn β hG).ne',Real.log_exp] at hh
  linarith

lemma latitudePartitionProfile_ge_entropy {n : ℕ} (β : ℝ) (H : Vector (n+1) → ℝ)
    (u : Vector (n+1)) {q : ℝ} (hq : |q|<1) :
    Real.log (partitionAgainst (latitudeLaw u (latitudeFrameAt u) q) β H)/((n+1:ℕ):ℝ)+
      Real.log (1-q^2)/2 ≤ latitudePartitionProfile n β H u q := by
  have hq2 : q^2<1 := by nlinarith [(abs_lt.mp hq).1,(abs_lt.mp hq).2]
  have hlog : Real.log (1-q^2) ≤ 0 := Real.log_nonpos (by linarith) (by nlinarith [sq_nonneg q])
  have hr : ((n-2:ℕ):ℝ)/(2*((n+1:ℕ):ℝ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h : ((n-2:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast (show n-2 ≤ n+1 by omega)
    nlinarith
  unfold latitudePartitionProfile
  have hm := mul_le_mul_of_nonpos_right hr hlog
  linarith

lemma latitudePartitionProfile_mul (n : ℕ) (β : ℝ) (H : Vector (n+1) → ℝ)
    (u : Vector (n+1)) (q : ℝ) :
    ((n+1:ℕ):ℝ)*latitudePartitionProfile n β H u q=
      Real.log (partitionAgainst (latitudeLaw u (latitudeFrameAt u) q) β H)+
        ((n-2:ℕ):ℝ)*Real.log (1-q^2)/2 := by
  unfold latitudePartitionProfile
  have h : ((n+1:ℕ):ℝ)≠0 := by positivity
  field_simp

/-- Every interior latitude admits a fixed positive closed window on
which the square-root field modulus and entropy loss are jointly small. -/
theorem exists_latitude_window {q β K η : ℝ} (hq : |q|<1) (hη : 0<η)
    {A : Set ℝ} (hA : IsOpen A) (hqA : q∈A) :
    ∃ w : ℝ,0<w ∧ -1<q-w ∧ q+w<1 ∧ Icc (q-w) (q+w) ⊆ A ∧
      ∀ r ∈ Icc (q-w) (q+w),
        4*|β| *K*Real.sqrt |r-q|+(Real.log (1-q^2)-Real.log (1-r^2))/2 ≤ η := by
  let f : ℝ → ℝ := fun r => 4*|β| *K*Real.sqrt |r-q|+
    (Real.log (1-q^2)-Real.log (1-r^2))/2
  have harg : 1-q^2≠0 := by nlinarith [(abs_lt.mp hq).1,(abs_lt.mp hq).2]
  have hc : ContinuousAt f q := by
    exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.sub continuous_const).abs)).continuousAt.add
      ((continuousAt_const.sub ((continuousAt_const.sub (continuousAt_id.pow 2)).log harg)).div_const 2)
  have hf : f q=0 := by simp [f]
  have hsmall : ∀ᶠ r in 𝓝 q,f r<η := by
    have h := hc.tendsto.eventually (gt_mem_nhds (show f q<η by rw [hf];exact hη))
    exact h
  have hnhds : {r : ℝ | r∈Ioo (-1:ℝ) 1 ∧ r∈A ∧ f r<η} ∈ 𝓝 q := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hq),hA.mem_nhds hqA,hsmall] with r hr hAr hfr
    exact ⟨hr,hAr,hfr⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hwin (r : ℝ) (hr : r∈Icc (q-δ/2) (q+δ/2)) :
      r∈Ioo (-1:ℝ) 1 ∧ r∈A ∧ f r<η := by
    apply hball
    rw [mem_ball,Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [hr.1,hr.2]
  refine ⟨δ/2,by positivity,(hwin _ ⟨le_rfl,by linarith⟩).1.1,
    (hwin _ ⟨by linarith,le_rfl⟩).1.2,?_,?_⟩
  · exact fun r hr => (hwin r hr).2.1
  · exact fun r hr => (hwin r hr).2.2.le

end SlowEquilibration.SphericalNestedLatitude
