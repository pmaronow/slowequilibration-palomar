module
public import FourPapersCommon.MixedMeasure
public import FourPapersCommon.MixtureAnalysis
public import FourPapersCommon.WeightedCDF
public import FourPapersCommon.AllFieldMinimizer

@[expose] public section

/-! Existence and strict uniqueness for the genuine mixed covariance functional.
The original overlap coordinate is retained in its weighted correction. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace FourPapersCommon

theorem continuous_parisiPotential_initial_allFields (β h : ℝ) :
    Continuous (fun μ : Paper.ParisiMeasure => Paper.parisiPotential β μ (0,h)) := by
  have he : (fun μ : Paper.ParisiMeasure => Paper.parisiPotential β μ (0,h)) =
      fun μ => Paper.parisiPDEFunctional β h μ - Real.log 2 +
        β^2/2 * weightedCDFIntegral (fun q => q) μ := by
    funext μ
    unfold Paper.parisiPDEFunctional Paper.parisiFunctional weightedCDFIntegral
    ring
  rw [he]
  exact ((FRSB.continuous_parisiPDEFunctional β h).sub continuous_const).add
    (continuous_const.mul (continuous_weightedCDFIntegral _ continuousOn_id))

theorem continuousOn_mixedCorrectionWeight (ξ : AdmissibleEvenMixture) :
    ContinuousOn (fun q : ℝ => q*ξ.second q) (Icc (0:ℝ) 1) :=
  continuousOn_id.mul (ξ.continuousOn_second.mono
    (fun _ hq => ⟨by linarith [hq.1],hq.2⟩))

theorem continuous_mixedPotential_initial (ξ : AdmissibleEvenMixture) (h : ℝ) :
    Continuous (fun μ : Paper.ParisiMeasure => mixedPotential ξ μ (0,h)) := by
  simpa only [mixedPotential,ξ.clock_zero,Function.comp_def] using
    (continuous_parisiPotential_initial_allFields (mixedBeta ξ) h).comp
      (continuous_mixedMeasure ξ)

theorem continuous_mixedFunctional (ξ : AdmissibleEvenMixture) (h : ℝ) :
    Continuous (mixedFunctional ξ h) := by
  exact (continuous_const.add (continuous_mixedPotential_initial ξ h)).sub
    (continuous_const.mul
      (continuous_weightedCDFIntegral _ (continuousOn_mixedCorrectionWeight ξ)))

theorem mixedFunctional_mix_lt (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) (hne : μ ≠ ν) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    mixedFunctional ξ h (Paper.parisiMix μ ν t) <
      (1-t)*mixedFunctional ξ h μ+t*mixedFunctional ξ h ν := by
  have hp := parisiPotential_initial_mix_lt_allFields (mixedBeta ξ) h
    (mixedBeta_ne_zero ξ) (mixedMeasure ξ μ) (mixedMeasure ξ ν)
    (fun he => hne (mixedMeasure_injective ξ he)) t ht
  rw [←mixedMeasure_mix ξ μ ν t ⟨ht.1.le,ht.2.le⟩] at hp
  have hc := weightedCDFIntegral_mix (fun q => q*ξ.second q)
    (continuousOn_mixedCorrectionWeight ξ) μ ν t ⟨ht.1.le,ht.2.le⟩
  simp only [weightedCDFIntegral] at hc
  simp only [mixedFunctional,mixedPotential,ξ.clock_zero]
  rw [hc]
  nlinarith

theorem exists_mixed_minimizer (ξ : AdmissibleEvenMixture) (h : ℝ) :
    ∃ μ : Paper.ParisiMeasure, IsMixedMinimizer ξ h μ := by
  obtain ⟨μ,_,hμ⟩ := (isCompact_univ : IsCompact (univ : Set Paper.ParisiMeasure)).exists_isMinOn
    (show (univ : Set Paper.ParisiMeasure).Nonempty from
      ⟨Paper.diracOverlap 0 (by norm_num),mem_univ _⟩)
    (continuous_mixedFunctional ξ h).continuousOn
  exact ⟨μ,fun ν => hμ (mem_univ ν)⟩

def mixedMinimizer (ξ : AdmissibleEvenMixture) (h : ℝ) : Paper.ParisiMeasure :=
  Classical.choose (exists_mixed_minimizer ξ h)

theorem isMixedMinimizer_selected (ξ : AdmissibleEvenMixture) (h : ℝ) :
    IsMixedMinimizer ξ h (mixedMinimizer ξ h) :=
  Classical.choose_spec (exists_mixed_minimizer ξ h)

theorem mixed_minimizer_eq (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ ν : Paper.ParisiMeasure) (hμ : IsMixedMinimizer ξ h μ)
    (hν : IsMixedMinimizer ξ h ν) : μ = ν := by
  by_contra hne
  have hs := mixedFunctional_mix_lt ξ h μ ν hne (1/2) (by norm_num)
  have he : mixedFunctional ξ h μ = mixedFunctional ξ h ν :=
    le_antisymm (hμ ν) (hν μ)
  have hm := hμ (Paper.parisiMix μ ν (1/2))
  rw [←he] at hs
  nlinarith

theorem mixedMinimizer_unique (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (hμ : IsMixedMinimizer ξ h μ) :
    μ = mixedMinimizer ξ h :=
  mixed_minimizer_eq ξ h μ _ hμ (isMixedMinimizer_selected ξ h)

theorem existsUnique_mixed_minimizer (ξ : AdmissibleEvenMixture) (h : ℝ) :
    ∃! μ : Paper.ParisiMeasure, IsMixedMinimizer ξ h μ :=
  ⟨mixedMinimizer ξ h,isMixedMinimizer_selected ξ h,
    fun μ hμ => mixedMinimizer_unique ξ h μ hμ⟩

theorem mixedMinimizer_value (ξ : AdmissibleEvenMixture) (h : ℝ) :
    mixedFunctional ξ h (mixedMinimizer ξ h) = mixedPressure ξ h := by
  have hb : BddBelow (range (mixedFunctional ξ h)) := by
    refine ⟨mixedFunctional ξ h (mixedMinimizer ξ h),?_⟩
    rintro r ⟨μ,rfl⟩
    exact isMixedMinimizer_selected ξ h μ
  unfold mixedPressure
  apply le_antisymm
  · apply le_csInf (show (range (mixedFunctional ξ h)).Nonempty from
      ⟨mixedFunctional ξ h (mixedMinimizer ξ h),⟨mixedMinimizer ξ h,rfl⟩⟩)
    rintro r ⟨μ,rfl⟩
    exact isMixedMinimizer_selected ξ h μ
  · exact csInf_le hb ⟨mixedMinimizer ξ h,rfl⟩

end FourPapersCommon
