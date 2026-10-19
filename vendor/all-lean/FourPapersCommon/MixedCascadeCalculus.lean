module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Targets.TalagrandCore

@[expose] public section

/-!
Covariance-independent cascade calculus for genuine Gaussian energy vectors.
The proofs are adapted from the Apache-2.0 frozen TalagrandCore source, replacing
its unused SK covariance structure by the actual Gaussian Hilbert representation.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

theorem mixed_hasDerivAt_guerraPhi {N : ℕ} (β h : ℝ) (U : Ω → EnergySpace N) (hg : IsGaussianHilbert U)
    {k : ℕ} (s : RSBScheme k) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (guerraPhi N s β h U)
      ((1 / (N : ℝ)) * ∫ ω, guerraD N s β (U ω) h (k + 2) t₀ 0 ∂ℙ) t₀ := by
  classical
  obtain ⟨a, b, hb, hbound⟩ := abs_guerraD_top_le N s β h ht₀ (k := k)
  obtain ⟨a₀, b₀, D, L, a', b', D', hb₀, -, -, -, -, hU⟩ :=
    guerra_cascade_hasDerivAt N s β h ht₀ (k + 2)
  have hUmeas : Measurable U := hg.repr_measurable
  have hnormint : Integrable (fun ω => ‖U ω‖) (ℙ : Measure Ω) :=
    PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian hg
  have hbint : Integrable (fun ω => a + b * ‖U ω‖) (ℙ : Measure Ω) :=
    (integrable_const _).add (hnormint.const_mul _)
  have hs : talNbhd t₀ ∈ 𝓝 t₀ := talNbhd_mem_nhds ht₀ (self_mem_talNbhd ht₀)
  have hb2 : Integrable (fun ω => a₀ + b₀ * (Fintype.card (Config N) * ‖U ω‖))
      (ℙ : Measure Ω) :=
    (integrable_const _).add ((hnormint.const_mul _).const_mul _)
  have hF0 : Integrable
      (fun ω => cascadeT N s β 1 (guerraBase N (U ω) h t₀) (k + 2) 0) (ℙ : Measure Ω) := by
    refine Integrable.mono hb2
      ((measurable_cascade_top_U s β h t₀).comp hUmeas).aestronglyMeasurable ?_
    filter_upwards with ω
    have h1 := (hU (U ω)).2.2.1 t₀ (self_mem_talNbhd ht₀) 0
    have h2 : l1 (0 : Fin N → ℝ) = 0 := by simp [l1]
    rw [h2, mul_zero, add_zero] at h1
    have h3 := mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm N (U ω)) hb₀
    have hnn : 0 ≤ a₀ + b₀ * (Fintype.card (Config N) * ‖U ω‖) := by
      linarith [abs_nonneg (cascadeT N s β 1 (guerraBase N (U ω) h t₀) (k + 2) 0)]
    show ‖cascadeT N s β 1 (guerraBase N (U ω) h t₀) (k + 2) 0‖
        ≤ ‖a₀ + b₀ * (Fintype.card (Config N) * ‖U ω‖)‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith
  have hmain : HasDerivAt
      (fun t => ∫ ω, cascadeT N s β 1 (guerraBase N (U ω) h t) (k + 2) 0 ∂ℙ)
      (∫ ω, guerraD N s β (U ω) h (k + 2) t₀ 0 ∂ℙ) t₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (ℙ : Measure Ω))
      (F := fun t ω => cascadeT N s β 1 (guerraBase N (U ω) h t) (k + 2) 0)
      (F' := fun t ω => guerraD N s β (U ω) h (k + 2) t 0)
      (bound := fun ω => a + b * ‖U ω‖) (s := talNbhd t₀) hs ?_ hF0 ?_ ?_ hbint ?_).2
    · filter_upwards [hs] with t ht
      exact ((measurable_cascade_top_U s β h t).comp hUmeas).aestronglyMeasurable
    · exact ((measurable_guerraD_top_U s β h t₀).comp hUmeas).aestronglyMeasurable
    · filter_upwards with ω t ht
      rw [Real.norm_eq_abs]
      exact hbound (U ω) t ht
    · filter_upwards with ω t ht
      exact hasDerivAt_cascade_top N s β (U ω) h (talNbhd_subset_Ioo ht₀ ht)
  show HasDerivAt (fun t => (1 / (N : ℝ))
      * ∫ ω, cascadeT N s β 1 (guerraBase N (U ω) h t) (k + 2) 0 ∂ℙ) _ t₀
  exact hmain.const_mul (1 / (N : ℝ))

theorem mixed_guerra_disorder_stein {N : ℕ} (β h : ℝ)
    (U : Ω → EnergySpace N) (hg : IsGaussianHilbert U) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (x : Fin N → ℝ) :
    (∫ ω, guerraUD N s β (U ω) (U ω) h t j x ∂ℙ) =
      ∑ i : hg.ι, (hg.τ i : ℝ) *
        ∫ ω, guerraUUD N s β (U ω) (hg.w i) (hg.w i) h t j x ∂ℙ := by
  classical
  let Φ := fun (i : hg.ι) U => guerraUD N s β U (hg.w i) h t j x
  let D := fun (i : hg.ι) U => guerraUUD N s β U (hg.w i) (hg.w i) h t j x
  have hΦm : ∀ i, Measurable (Φ i) := fun i =>
    (measurable_guerraUD_joint s β (hg.w i) h t j).comp
      (measurable_id.prodMk measurable_const)
  have hDm : ∀ i, Measurable (D i) := fun i =>
    (measurable_guerraUUD_joint s β (hg.w i) (hg.w i) h t j).comp
      (measurable_id.prodMk measurable_const)
  have hC : ∀ i, 0 ≤ Real.sqrt t * uAbs N (hg.w i) := fun i =>
    mul_nonneg (Real.sqrt_nonneg _) (uAbs_nonneg N _)
  have hΦb : ∀ i U, |Φ i U| ≤ Real.sqrt t * uAbs N (hg.w i) + 0 * ‖U‖ := by
    intro i U
    simpa only [zero_mul, add_zero] using
      (guerraUD_measurable_and_bound N s β U (hg.w i) h ht j).2 x
  have hintCoord : ∀ i, Integrable (fun ω => hg.c i ω * Φ i (U ω)) ℙ := fun i =>
    integrable_coord_mul_comp_of_affine_norm_bound hg i (hΦm i) (hC i) le_rfl (hΦb i)
  have hintΦ : ∀ i, Integrable (fun ω => Φ i (U ω)) ℙ := fun i =>
    integrable_comp_of_affine_norm_bound hg (hΦm i) (hC i) le_rfl (hΦb i)
  have hintD : ∀ i, Integrable (fun ω => D i (U ω)) ℙ := by
    intro i
    refine integrable_comp_of_affine_norm_bound hg (hDm i)
      (guerraUUBound_nonneg N (hg.w i) (hg.w i) t j) (D := 0) le_rfl ?_
    intro U
    simpa only [zero_mul, add_zero] using
      abs_guerraUUD_le N s β U (hg.w i) (hg.w i) h ht j x
  have hexpand : ∀ ω, guerraUD N s β (U ω) (U ω) h t j x =
      ∑ i, hg.c i ω * Φ i (U ω) := by
    intro ω
    have hrepr : U ω = ∑ i, hg.c i ω • hg.w i := congrFun hg.repr ω
    calc
      guerraUD N s β (U ω) (U ω) h t j x =
          guerraUD N s β (U ω) (∑ i, hg.c i ω • hg.w i) h t j x :=
        congrArg (fun V => guerraUD N s β (U ω) V h t j x) hrepr
      _ = _ := guerraUD_sum_smul N s β (U ω) h ht (fun i => hg.c i ω) hg.w j x
  calc
    (∫ ω, guerraUD N s β (U ω) (U ω) h t j x ∂ℙ) =
        ∫ ω, ∑ i, hg.c i ω * Φ i (U ω) ∂ℙ :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = _ := stein_sum_of_hasDerivAt hg
      (fun i U r => hasDerivAt_guerraUD_Uline N s β U (hg.w i) (hg.w i) h ht j x r)
      hΦm hDm hintCoord hintΦ hintD

theorem mixed_continuousOn_guerraPhi {N : ℕ} (β h : ℝ)
    (U : Ω → EnergySpace N) (hg : IsGaussianHilbert U) {k : ℕ} (s : RSBScheme k) :
    ContinuousOn (guerraPhi N s β h U) (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨a, D, hD, hprops⟩ := guerra_cascade_continuous_Icc N s β h (k + 2)
  have hc : ContinuousOn (fun t => ∫ ω,
      cascadeT N s β 1 (guerraBase N (U ω) h t) (k + 2) 0 ∂ℙ) (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_dominated (bound := fun ω => a + Fintype.card (Config N) * ‖U ω‖)
    · intro t _
      exact ((measurable_cascade_top_U s β h t).comp hg.repr_measurable).aestronglyMeasurable
    · intro t ht
      filter_upwards with ω
      have hb := (hprops (U ω)).2.1 t ht 0
      simp only [l1, Pi.zero_apply, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at hb
      rw [Real.norm_eq_abs]
      exact hb.trans (add_le_add_right (uAbs_le_card_mul_norm N (U ω)) a)
    · exact (integrable_const a).add
        ((PhysLean.Probability.GaussianIBP.integrable_norm_of_gaussian hg).const_mul _)
    · exact Filter.Eventually.of_forall (fun ω => (hprops (U ω)).2.2 0)
  exact hc.const_mul (1 / (N : ℝ))

theorem mixed_integrable_guerraReplicaAccum {N : ℕ} (β h : ℝ)
    (U : Ω → EnergySpace N) (hg : IsGaussianHilbert U) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {K : ℕ → Config N → Config N → ℝ}
    {C : ℝ} (hK : ∀ l σ τ, |K l σ τ| ≤ C) (j : ℕ) (y : Fin N → ℝ) :
    Integrable (fun ω => guerraReplicaAccum N s β (U ω) h t K j y) (ℙ : Measure Ω) := by
  have hC : 0 ≤ C := (abs_nonneg (K 0 default default)).trans (hK 0 _ _)
  apply integrable_comp_of_affine_norm_bound hg
    ((measurable_guerraReplicaAccum_joint s β h t K j).comp
      (f := fun U : EnergySpace N => (U, y)) (measurable_id.prodMk measurable_const))
    (C := C * (1 - guerraMass s j)) (D := 0)
    (mul_nonneg hC (sub_nonneg.mpr (guerraMass_mem_Icc s j).2)) le_rfl
  intro U
  simpa only [Function.comp_apply, zero_mul, add_zero] using guerraReplicaAccum_abs_le N s β U h ht hC hK j y

theorem mixed_integrable_guerraUD_radial {N : ℕ} (β h : ℝ)
    (U : Ω → EnergySpace N) (hg : IsGaussianHilbert U) {k : ℕ} (s : RSBScheme k)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (y : Fin N → ℝ) :
    Integrable (fun ω => guerraUD N s β (U ω) (U ω) h t j y) (ℙ : Measure Ω) := by
  have hm : Measurable (fun U : EnergySpace N => guerraUD N s β U U h t j y) := by
    have he : (fun U : EnergySpace N => guerraUD N s β U U h t j y) =
        fun U => Real.sqrt t * ∑ σ : Config N, guerraProb N s β U h t j σ y * U σ := by
      funext U
      exact guerraUD_eq_mean N s β U U h ht j y
    rw [he]
    exact (Finset.measurable_sum _ (fun σ _ =>
      ((measurable_guerraProb_joint s β h t j σ).comp
        (f := fun U : EnergySpace N => (U, y)) (measurable_id.prodMk measurable_const)).mul
      (measurable_coord N σ))).const_mul _
  apply integrable_comp_of_affine_norm_bound hg hm (C := 0)
    (D := Real.sqrt t * Fintype.card (Config N)) le_rfl (by positivity)
  intro U
  calc
    _ ≤ Real.sqrt t * uAbs N U := (guerraUD_measurable_and_bound N s β U U h ht j).2 y
    _ ≤ Real.sqrt t * (Fintype.card (Config N) * ‖U‖) :=
      mul_le_mul_of_nonneg_left (uAbs_le_card_mul_norm N U) (Real.sqrt_nonneg _)
    _ = _ := by ring

end FourPapersCommon
