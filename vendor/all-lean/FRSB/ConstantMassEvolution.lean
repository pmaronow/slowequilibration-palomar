module
public import FRSB.FiniteSchemeRepresentation
public import FRSB.GlobalMeasureStability
public import Paper.ParisiPotentialStability
public import FRSB.PotentialMeasureContinuity
public import FRSB.ConstantMassGrowth

@[expose] public section

/-! Literal Cole--Hopf evolution of the selected Parisi potential on an
actual constant-CDF interval. Endpoint atoms are retained. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology NNReal
namespace FRSB
open Paper SpinGlass.Targets
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory

theorem notMem_support_of_cdf_constant (μ : ParisiMeasure) {r t m : ℝ} (hrt : r < t)
    (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m)
    (q : Overlap) (hq : (q : ℝ) ∈ Ioo r t) : q ∉ (μ : Measure Overlap).support := by
  let b : ℝ := ((q : ℝ) + t) / 2
  have hqb : (q : ℝ) < b := by dsimp [b]; linarith [hq.2]
  have hb : b < t := by dsimp [b]; linarith [hq.2]
  have hrb : r < b := hq.1.trans hqb
  have hp : ((μ : Measure Overlap).map Subtype.val) (Ioc r b) = 0 := by
    rw [← measure_cdf ((μ : Measure Overlap).map Subtype.val), StieltjesFunction.measure_Ioc,
      ← parisiCDF_eq_realCDF μ b, ← parisiCDF_eq_realCDF μ r,
      hc b ⟨hrb.le, hb⟩, hc r ⟨le_rfl, hrt⟩, sub_self]
    simp
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Ioc] at hp
  have hu : IsOpen {y : Overlap | (y : ℝ) ∈ Ioo r b} :=
    isOpen_Ioo.preimage continuous_subtype_val
  have hz : (μ : Measure Overlap) {y : Overlap | (y : ℝ) ∈ Ioo r b} = 0 :=
    measure_mono_null (show {y : Overlap | (y : ℝ) ∈ Ioo r b} ⊆
      Subtype.val ⁻¹' Ioc r b from fun y hy => ⟨hy.1, hy.2.le⟩) hp
  intro hqs
  have hpos := (Measure.mem_support_iff_forall q).mp hqs
    {y : Overlap | (y : ℝ) ∈ Ioo r b}
    (hu.mem_nhds (show q ∈ {y : Overlap | (y : ℝ) ∈ Ioo r b} from ⟨hq.1, hqb⟩))
  rw [hz] at hpos
  exact lt_irrefl _ hpos

theorem parisiMeasure_open_interval_eq_zero_of_cdf_constant (μ : ParisiMeasure)
    {r t m : ℝ} (hrt : r < t) (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) :
    (μ : Measure Overlap) {q | (q : ℝ) ∈ Ioo r t} = 0 := by
  apply (measure_eq_zero_iff_ae_notMem).mpr
  filter_upwards [(μ : Measure Overlap).support_mem_ae] with q hq
  exact fun hi => notMem_support_of_cdf_constant μ hrt hc q hi hq

theorem parisiCDF_eq_left_of_interval_mass_zero (μ : ParisiMeasure) {r t : ℝ}
    (hz : (μ : Measure Overlap) {q | (q : ℝ) ∈ Ioo r t} = 0)
    {s : ℝ} (hs : s ∈ Ico r t) : parisiCDF μ s = parisiCDF μ r := by
  have he : {q : Overlap | (q : ℝ) ≤ s} =ᵐ[(μ : Measure Overlap)]
      {q : Overlap | (q : ℝ) ≤ r} := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hz] with q hq
    apply propext
    constructor
    · intro hqs
      by_contra hn
      exact hq ⟨not_le.mp hn, hqs.trans_lt hs.2⟩
    · exact fun hqr => hqr.trans hs.1
  unfold parisiCDF
  rw [measure_congr he]

theorem exists_finiteLaw_cell_covering_gap (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ 1)
    (hgap : ∀ q : Overlap, (q : ℝ) ∈ Ioo r t → q ∉ (μ : Measure Overlap).support) :
    ∃ p, p ≤ (finiteLawNodes μ hμ).card + 1 ∧
      (finiteLawRSBScheme μ hμ).q p ≤ r ∧ t ≤ (finiteLawRSBScheme μ hμ).q (p + 1) ∧
      (finiteLawRSBScheme μ hμ).q p < (finiteLawRSBScheme μ hμ).q (p + 1) := by
  obtain ⟨p, hp, hcell, hpos⟩ := exists_parisiFinite_right_cell (finiteLawRSBScheme μ hμ)
    (t := r) ⟨hr, hrt.trans_le ht⟩
  refine ⟨p, hp, hcell.1, ?_, hpos⟩
  by_contra hn
  have hp0 : 0 < p := by
    by_contra hh
    have he : p = 0 := by omega
    rw [he] at hcell
    change r ∈ Ico (finiteLawSchemeOverlap μ hμ 0) (finiteLawSchemeOverlap μ hμ 1) at hcell
    simp only [finiteLawSchemeOverlap_zero, finiteLawSchemeOverlap_at_index μ hμ
      ⟨0, finiteLawNodes_card_pos μ hμ⟩, finiteLawNodeEmbedding_zero, overlapZero] at hcell
    linarith [hcell.1, hcell.2]
  have hpC : p < (finiteLawNodes μ hμ).card := by
    by_contra hh
    have hone : (finiteLawRSBScheme μ hμ).q (p + 1) = 1 :=
      finiteLawSchemeOverlap_top μ hμ (by omega)
    rw [hone] at hn
    exact hn ht
  let q : Overlap := finiteLawNodeEmbedding μ hμ ⟨p, hpC⟩
  have hqeq : (finiteLawRSBScheme μ hμ).q (p + 1) = (q : ℝ) :=
    finiteLawSchemeOverlap_at_index μ hμ ⟨p, hpC⟩
  have hqi : (q : ℝ) ∈ Ioo r t := by rw [hqeq] at hcell hn; exact ⟨hcell.2, not_le.mp hn⟩
  have hqS : q ∈ finiteLawNodes μ hμ :=
    (finiteLawNodes μ hμ).orderEmbOfFin_mem rfl ⟨p, hpC⟩
  have hqs : q ∈ (μ : Measure Overlap).support := by
    simp only [finiteLawNodes, Finset.mem_insert, Set.Finite.mem_toFinset] at hqS
    rcases hqS with hqS | hqS | hqS
    · have hz : (q : ℝ) = 0 := by rw [hqS]; rfl
      linarith [hqi.1]
    · have ho : (q : ℝ) = 1 := by rw [hqS]; rfl
      linarith [hqi.2]
    · exact hqS
  exact hgap q hqi hqs

theorem parisiSlabPotential_eq_coleHopf {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b t x : ℝ) (ht : t ≤ b) :
    parisiSlabPotential s β j m b t x =
      coleHopf m (β ^ 2 * (b - t)).toNNReal (parisiF s β j) x := by
  have hvar : 0 ≤ β ^ 2 * (b - t) := mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht)
  have he := parisiStep_eq_coleHopf m (β ^ 2 * (b - t)).toNNReal (parisiF_measurable s β j) x
  rw [Real.coe_toNNReal _ hvar] at he
  exact he

theorem parisiSlabPotential_coleHopf_evolution {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (j : ℕ) (m b r t x : ℝ) (hrt : r ≤ t) (ht : t ≤ b) :
    parisiSlabPotential s β j m b r x =
      coleHopf m (β ^ 2 * (t - r)).toNNReal (parisiSlabPotential s β j m b t) x := by
  have hfun : parisiSlabPotential s β j m b t =
      coleHopf m (β ^ 2 * (b - t)).toNNReal (parisiF s β j) :=
    funext (fun y => parisiSlabPotential_eq_coleHopf s β j m b t y ht)
  have hgrowth : HasLinearGrowth (parisiF s β j) := by
    obtain ⟨B, C, hB, hC, h⟩ := parisiF_hasLinearGrowth s β j
    exact ⟨B, C, hC, h⟩
  rw [hfun, coleHopf_coleHopf hgrowth (parisiF_measurable s β j),
    parisiSlabPotential_eq_coleHopf s β j m b r x (hrt.trans ht)]
  congr 2
  apply NNReal.eq
  rw [NNReal.coe_add,
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hrt)),
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht)),
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (hrt.trans ht)))]
  ring

/-- Literal selected-potential Cole--Hopf evolution for any finite law. -/
theorem parisiPotential_coleHopf_of_finite_support (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    {r t m : ℝ} (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ 1)
    (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) (x : ℝ) :
    parisiPotential β μ (r, x) = coleHopf m (β ^ 2 * (t - r)).toNNReal
      (fun y => parisiPotential β μ (t, y)) x := by
  obtain ⟨p, hp, hpr, htp, hpos⟩ := exists_finiteLaw_cell_covering_gap μ hμ hr hrt ht
    (fun q hq => notMem_support_of_cdf_constant μ hrt hc q hq)
  let s := finiteLawRSBScheme μ hμ
  have hrI : r ∈ Icc (s.q p) (s.q (p + 1)) := ⟨hpr, hrt.le.trans htp⟩
  have htI : t ∈ Icc (s.q p) (s.q (p + 1)) := ⟨hpr.trans hrt.le, htp⟩
  have hm : s.m p = m := by
    have he := parisiCDF_scheme_cell s hp ⟨hpr, hrt.trans_le htp⟩
    rw [parisiSchemeMeasure_finiteLawRSBScheme] at he
    exact he.symm.trans (hc r ⟨le_rfl, hrt⟩)
  have hfun : (fun y => parisiPotential β μ (t, y)) =
      parisiSlabPotential s β ((finiteLawNodes μ hμ).card + 1 - p)
        m (s.q (p + 1)) t := by
    funext y
    rw [parisiPotential_finiteLawRSBScheme β hβ μ hμ t y ⟨hr.trans hrt.le, ht⟩,
      parisiFinitePotential_eq_slab s β hp hpos htI, hm]
  rw [hfun, parisiPotential_finiteLawRSBScheme β hβ μ hμ r x ⟨hr, hrt.le.trans ht⟩,
    parisiFinitePotential_eq_slab s β hp hpos hrI, hm]
  exact parisiSlabPotential_coleHopf_evolution s β _ m (s.q (p + 1)) r t x hrt.le htp

theorem parisiPotential_hasLinearGrowth (β : ℝ) (μ : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : HasLinearGrowth (fun x => parisiPotential β μ (t, x)) :=
  ⟨β ^ 2, 1, zero_le_one, fun x => by
    simpa only [one_mul] using parisiPotential_absolute_growth β μ t x ht⟩

/-- Genuine Cole--Hopf evolution for every probability measure, including
constant mass zero and an atom at the terminal time. -/
theorem parisiPotential_coleHopf_on_constantCDF (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {r t m : ℝ} (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ 1)
    (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) (x : ℝ) :
    parisiPotential β μ (r, x) = coleHopf m (β ^ 2 * (t - r)).toNNReal
      (fun y => parisiPotential β μ (t, y)) x := by
  let rO : Overlap := ⟨r, hr, hrt.le.trans ht⟩
  let tO : Overlap := ⟨t, hr.trans hrt.le, ht⟩
  let S : Finset Overlap := {rO, tO}
  let ν := preservingMeasure μ S
  have hν : Tendsto ν atTop (𝓝 μ) := tendsto_preservingMeasure μ S
  have hzero := parisiMeasure_open_interval_eq_zero_of_cdf_constant μ hrt hc
  have hzeron (n : ℕ) : (ν n : Measure Overlap) {q | (q : ℝ) ∈ Ioo r t} = 0 := by
    change (preservingMeasure μ S n : Measure Overlap) (Ioo rO tO) = 0
    rw [preservingMeasure_open_interval_mass μ S n rO tO (by simp [S]) (by simp [S])]
    exact hzero
  have hcn (n : ℕ) (s : ℝ) (hs : s ∈ Ico r t) : parisiCDF (ν n) s = m := by
    rw [parisiCDF_eq_left_of_interval_mass_zero (ν n) (hzeron n) hs]
    have he := preservingMeasure_cdf_mass μ S n rO (by simp [S])
    exact he.trans (hc r ⟨le_rfl, hrt⟩)
  have hn (n : ℕ) : parisiPotential β (ν n) (r, x) =
      coleHopf m (β ^ 2 * (t - r)).toNNReal
        (fun y => parisiPotential β (ν n) (t, y)) x :=
    parisiPotential_coleHopf_of_finite_support β hβ (ν n)
      (finite_support_preservingMeasure μ S n) hr hrt ht (hcn n) x
  have hlim : Tendsto (fun n => coleHopf m (β ^ 2 * (t - r)).toNNReal
      (fun y => parisiPotential β (ν n) (t, y)) x) atTop
        (𝓝 (coleHopf m (β ^ 2 * (t - r)).toNNReal
          (fun y => parisiPotential β μ (t, y)) x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => ?_) (tendsto_parisiPotentialMeasureError_of_weak β μ ν hν)
    rw [Real.norm_eq_abs]
    apply abs_coleHopf_sub_le_of_sup
      (parisiPotential_hasLinearGrowth β (ν n) t ⟨hr.trans hrt.le, ht⟩)
      ((continuous_parisiPotential β (ν n)).comp (continuous_const.prodMk continuous_id)).measurable
      (parisiPotential_hasLinearGrowth β μ t ⟨hr.trans hrt.le, ht⟩)
      ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)).measurable
    intro y
    simpa only [Real.norm_eq_abs] using
      parisiPotential_measure_error_bound β (ν n) μ t y ⟨hr.trans hrt.le, ht⟩
  exact tendsto_nhds_unique (tendsto_parisiPotential_of_weak β μ ν hν r x ⟨hr, hrt.le.trans ht⟩)
    (hlim.congr' (Eventually.of_forall fun n => (hn n).symm))

/-- The closed-interval form includes zero elapsed time and terminal atoms. -/
theorem parisiPotential_coleHopf_constant_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m)
    {r t : ℝ} (hr : r ∈ Icc a b) (ht : t ∈ Icc r b) (x : ℝ) :
    parisiPotential β μ (r, x) = coleHopf m (β ^ 2 * (t - r)).toNNReal
      (fun y => parisiPotential β μ (t, y)) x := by
  rcases eq_or_lt_of_le ht.1 with he | hrt
  · subst t
    simp
  · exact parisiPotential_coleHopf_on_constantCDF β hβ μ (ha.trans hr.1) hrt
      (ht.2.trans hb) (fun s hs => hc s ⟨hr.1.trans hs.1, hs.2.trans_le ht.2⟩) x

theorem gaussian_shift_average_eq_heat (v : ℝ≥0) (A : ℝ → ℝ) (hA : Measurable A) (x : ℝ) :
    (∫ z, A (x + z) ∂gaussianReal 0 v) = Paper.heatSemigroup v A x := by
  have hm : (gaussianReal 0 v).map (fun z : ℝ => x + z) = gaussianReal x v := by
    simpa using (gaussianReal_map_const_add (μ := 0) (v := v) x)
  calc
    _ = ∫ y, A y ∂gaussianReal x v := by
      rw [← hm, integral_map (by fun_prop) hA.aestronglyMeasurable]
    _ = Paper.heatSemigroup (v : ℝ) A x := by
      simpa only [Real.toNNReal_coe] using
        (Paper.heatSemigroup_eq_gaussian_integral (v : ℝ) v.property A hA x).symm

/-- **Lemma 2.4(i)**, positive-mass literal exponential heat identity. -/
theorem parisiPotential_exp_heat_on_constant_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hm : 0 < m) (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m)
    {r t : ℝ} (hr : r ∈ Icc a b) (ht : t ∈ Icc r b) (x : ℝ) :
    Real.exp (m * parisiPotential β μ (r, x)) =
      Paper.heatSemigroup (β ^ 2 * (t - r)) (fun y => Real.exp (m * parisiPotential β μ (t, y))) x := by
  rw [parisiPotential_coleHopf_constant_interval β hβ μ ha hab hb hc hr ht x,
    exp_mul_coleHopf (parisiPotential_hasLinearGrowth β μ t ⟨ha.trans (hr.1.trans ht.1), ht.2.trans hb⟩)
      ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)).measurable hm.ne']
  have he := gaussian_shift_average_eq_heat (β ^ 2 * (t - r)).toNNReal
      (fun y => Real.exp (m * parisiPotential β μ (t, y)))
      (((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)).measurable.const_mul m).exp x
  rw [Real.coe_toNNReal (β ^ 2 * (t - r)) (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.1))] at he
  exact he

/-- **Lemma 2.4(i)**, mass-zero literal heat identity. -/
theorem parisiPotential_heat_on_zeroCDF_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = 0)
    {r t : ℝ} (hr : r ∈ Icc a b) (ht : t ∈ Icc r b) (x : ℝ) :
    parisiPotential β μ (r, x) =
      Paper.heatSemigroup (β ^ 2 * (t - r)) (fun y => parisiPotential β μ (t, y)) x := by
  rw [parisiPotential_coleHopf_constant_interval β hβ μ ha hab hb hc hr ht x, coleHopf_zero]
  have he := gaussian_shift_average_eq_heat (β ^ 2 * (t - r)).toNNReal
      (fun y => parisiPotential β μ (t, y))
      ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)).measurable x
  rw [Real.coe_toNNReal (β ^ 2 * (t - r)) (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.1))] at he
  exact he

end FRSB
