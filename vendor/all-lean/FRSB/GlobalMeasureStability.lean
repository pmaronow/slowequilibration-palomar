module
public import Paper.ParisiMixContinuity
public import Paper.ParisiPotentialStability
public import Paper.ParisiSpatialSmooth
public import FRSB.ParisiMeasureTopology

@[expose] public section

/-! Uniform continuity of the actual solution under CDF L1 variation. -/
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped Topology BoundedContinuousFunction
namespace FRSB

theorem norm_globalParisi_pair_mesh_le (β : ℝ) (μ ν : ParisiMeasure)
    (U V : ParisiSlabGradient 0 1) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hmildU : IsParisiMildOnEverySlab β μ U)
    (hmildV : IsParisiMildOnEverySlab β ν V)
    (hterminalU : ∀ x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) U (1, x) = Real.tanh x)
    (hterminalV : ∀ x, parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (1, x) = Real.tanh x)
    (N : ℕ) (hN : 0 < N)
    (hmesh : |β| * gaussianAbsMoment * Real.sqrt (1 / (N : ℝ)) ≤ 1 / 8)
    (δ : ℝ) (hδ : 0 < δ) (hCDF : parisiCDFDistance μ ν ≤ δ) :
    ‖U - V‖ ≤ parisiBackwardError N
      (12 * |β| * gaussianAbsMoment * Real.sqrt δ) := by
  let E := 12 * |β| * gaussianAbsMoment * Real.sqrt (δ)
  have hE : 0 ≤ E := by dsimp [E]; have := gaussianAbsMoment_nonneg; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hind : ∀ j : ℕ, j ≤ N → ∀ t ∈ Icc (1 - (j : ℝ) / N) 1, ∀ x : ℝ,
      ‖parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) U (t, x) -
        parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (t, x)‖ ≤
          parisiBackwardError j E := by
    intro j
    induction j with
    | zero =>
        intro _ t ht x
        have htone : t = 1 := le_antisymm ht.2 (by simpa using ht.1)
        subst t
        simp [hterminalU, hterminalV, parisiBackwardError]
    | succ j ih =>
        intro hj t ht x
        have hj' : j ≤ N := by omega
        have hcast : (j + 1 : ℝ) ≤ N := by exact_mod_cast hj
        let a : ℝ := 1 - (j + 1 : ℝ) / N
        let b : ℝ := 1 - (j : ℝ) / N
        have ha : 0 ≤ a := by
          dsimp [a]
          linarith [(div_le_one hNpos).mpr hcast]
        have hab : a ≤ b := by
          dsimp [a, b]
          exact sub_le_sub_left (div_le_div_of_nonneg_right (by linarith) hNpos.le) 1
        have hb : b ≤ 1 := by
          dsimp [b]
          linarith [div_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hNpos.le]
        have hba : b - a = 1 / (N : ℝ) := by dsimp [a, b]; ring
        let A := parisiGlobalRestrict ha hb U
        let Z := parisiGlobalRestrict ha hb V
        let g := fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) U (b, y)
        let k := fun y => parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) V (b, y)
        have hg : Continuous g := (continuous_parisiSlabExtend (by norm_num) U).comp (by fun_prop)
        have hk : Continuous k := (continuous_parisiSlabExtend (by norm_num) V).comp (by fun_prop)
        have hgb : ∀ y, ‖g y‖ ≤ 1 := fun y => (norm_parisiSlabExtend_le (by norm_num) U _).trans hU
        have hkb : ∀ y, ‖k y‖ ≤ 1 := fun y => (norm_parisiSlabExtend_le (by norm_num) V _).trans hV
        have hshort : parisiSlabContractionConstant β a b ≤ 1 / 8 := by
          simpa only [parisiSlabContractionConstant, hba] using hmesh
        have hA : ‖A‖ ≤ 2 := (norm_parisiGlobalRestrict_le ha hb U).trans (hU.trans (by norm_num))
        have hZ : ‖Z‖ ≤ 2 := (norm_parisiGlobalRestrict_le ha hb V).trans (hV.trans (by norm_num))
        have hv := globalParisiRestriction_fixedPoint β μ U hU hmildU hab ha hb
        have hz := globalParisiRestriction_fixedPoint β ν V hV hmildV hab ha hb
        have hdiff := localParisiGradient_terminal_measure_mesh_stability β
          μ ν hab ha hb g k hg hk hgb hkb
          hshort A Z hA hZ hv hz (parisiBackwardError j E)
          (fun y => ih hj' b ⟨le_rfl, hb⟩ y) δ hδ hCDF
        have ht' : t ∈ Icc a 1 := by simpa only [Nat.cast_add, Nat.cast_one] using ht
        by_cases htb : t ≤ b
        · have hp := (A - Z).norm_coe_le_norm (⟨t, ⟨ht'.1, htb⟩⟩, x)
          change ‖A (⟨t, ⟨ht'.1, htb⟩⟩, x) - Z (⟨t, ⟨ht'.1, htb⟩⟩, x)‖ ≤ _ at hp
          rw [parisiGlobalRestrict_apply, parisiGlobalRestrict_apply] at hp
          exact hp.trans hdiff
        · exact (ih hj' t ⟨(lt_of_not_ge htb).le, ht'.2⟩ x).trans
            (parisiBackwardError_le_succ j E hE)
  apply (BoundedContinuousFunction.norm_le (parisiBackwardError_nonneg N E hE)).mpr
  intro p
  have hpt : (p.1 : ℝ) ∈ Icc (1 - (N : ℝ) / N) 1 := by
    simpa only [div_self hNne, sub_self] using p.1.property
  have h := hind N le_rfl p.1 hpt p.2
  change ‖U p - V p‖ ≤ _
  simpa only [parisiSlabExtend, projIcc_of_mem _ p.1.property] using h


theorem exists_gradientBCF_mesh_bound (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (μ ν : ParisiMeasure) (δ : ℝ), 0 < δ →
      parisiCDFDistance μ ν ≤ δ →
      ‖parisiGradientBCF β μ - parisiGradientBCF β ν‖ ≤ M * Real.sqrt δ := by
  let c := |β| * gaussianAbsMoment
  have hc : 0 ≤ c := mul_nonneg (abs_nonneg β) gaussianAbsMoment_nonneg
  obtain ⟨N, hN⟩ := exists_nat_gt (64 * c ^ 2 + 1)
  have hNpos : (0 : ℝ) < N := by nlinarith [sq_nonneg c]
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hratio : c ^ 2 / (N : ℝ) < (1 / 8 : ℝ) ^ 2 :=
    (div_lt_iff₀ hNpos).mpr (by nlinarith)
  have hsquare : (c * Real.sqrt (1 / (N : ℝ))) ^ 2 = c ^ 2 / (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    ring
  have hmesh : |β| * gaussianAbsMoment * Real.sqrt (1 / (N : ℝ)) ≤ 1 / 8 := by
    change c * Real.sqrt (1 / (N : ℝ)) ≤ 1 / 8
    have hp := mul_nonneg hc (Real.sqrt_nonneg (1 / (N : ℝ)))
    nlinarith
  let M := ((2 : ℝ) ^ N - 1) * (12 * |β| * gaussianAbsMoment)
  have hp : 0 ≤ (2 : ℝ) ^ N - 1 := by
    simpa only [parisiBackwardError_eq, mul_one] using
      parisiBackwardError_nonneg N 1 (by norm_num)
  have hM : 0 ≤ M := by
    exact mul_nonneg hp
      (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg β)) gaussianAbsMoment_nonneg)
  refine ⟨M, hM, ?_⟩
  intro μ ν δ hδ hCDF
  have h := norm_globalParisi_pair_mesh_le β μ ν
    (parisiGradientBCF β μ) (parisiGradientBCF β ν)
    (norm_parisiGradientBCF_le_one β μ) (norm_parisiGradientBCF_le_one β ν)
    (parisiGradientBCF_mildOnEverySlab_all β μ)
    (parisiGradientBCF_mildOnEverySlab_all β ν)
    (parisiGradient_terminal β μ) (parisiGradient_terminal β ν)
    N hNnat hmesh δ hδ hCDF
  simpa only [parisiBackwardError_eq, M, mul_assoc] using h

/-- CDF L1 convergence controls the actual gradient on the entire closed strip. -/
theorem tendsto_gradientBCF_of_CDFDistance {A : Type*} {l : Filter A}
    (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hCDF : Tendsto (fun a => parisiCDFDistance μ (ν a)) l (𝓝 0)) :
    Tendsto (fun a => parisiGradientBCF β (ν a)) l (𝓝 (parisiGradientBCF β μ)) := by
  obtain ⟨M, hM, hbound⟩ := exists_gradientBCF_mesh_bound β
  have herr : Tendsto (fun n : ℕ => M * Real.sqrt (1 / (n + 1 : ℕ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (herr.eventually (eventually_lt_nhds hε)).exists
  have hδ : (0 : ℝ) < 1 / (n + 1 : ℕ) := by positivity
  filter_upwards [hCDF.eventually (eventually_lt_nhds hδ)] with a ha
  rw [dist_eq_norm, norm_sub_rev]
  exact (hbound μ (ν a) _ hδ ha.le).trans_lt hn

/-- Continuity is in the usual weak topology on actual probability measures. -/
theorem continuous_gradientBCF (β : ℝ) : Continuous (parisiGradientBCF β) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply tendsto_gradientBCF_of_CDFDistance β μ id
  simpa only [parisiCDFDistance, abs_sub_comm] using
    (tendsto_parisiCDFDistance_of_tendsto (μ := μ) tendsto_id)

theorem norm_translate_gradient_sub_le (β : ℝ) (μ ν : ParisiMeasure) (s t : ℝ) :
    ‖bcfTranslate s (parisiGradientBCF β μ) -
      bcfTranslate t (parisiGradientBCF β ν)‖ ≤
      ‖parisiGradientBCF β μ - parisiGradientBCF β ν‖ + |s - t| := by
  have hsub : bcfTranslate s (parisiGradientBCF β μ) -
      bcfTranslate s (parisiGradientBCF β ν) =
      bcfTranslate s (parisiGradientBCF β μ - parisiGradientBCF β ν) := by
    ext p
    rfl
  have hL := (lipschitzWith_bcfTranslate (parisiGradientBCF β ν)
    (lipschitzWith_parisiGradientBCF_spatial β ν)).dist_le_mul s t
  rw [dist_eq_norm, Real.dist_eq] at hL
  calc
    _ ≤ ‖bcfTranslate s (parisiGradientBCF β μ) - bcfTranslate s (parisiGradientBCF β ν)‖ +
        ‖bcfTranslate s (parisiGradientBCF β ν) - bcfTranslate t (parisiGradientBCF β ν)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      rw [hsub, norm_bcfTranslate]
      exact add_le_add (le_refl _) (by simpa using hL)

theorem continuous_translated_gradientBCF (β : ℝ) :
    Continuous (fun p : ParisiMeasure × ℝ => bcfTranslate p.2 (parisiGradientBCF β p.1)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _)
  · exact Eventually.of_forall (fun q => norm_translate_gradient_sub_le β q.1 p.1 q.2 p.2)
  · have hμ : ContinuousAt (fun q : ParisiMeasure × ℝ => parisiGradientBCF β q.1) p :=
      ((continuous_gradientBCF β).comp continuous_fst).continuousAt
    have hs := continuous_snd.continuousAt (x := p)
    simpa only [sub_self, norm_zero, abs_zero, zero_add] using
      (hμ.tendsto.sub (tendsto_const_nhds (x := parisiGradientBCF β p.1))).norm.add
        (hs.tendsto.sub (tendsto_const_nhds (x := p.2))).abs

end FRSB
