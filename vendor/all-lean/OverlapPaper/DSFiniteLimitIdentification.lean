module

public import OverlapPaper.DSEmpiricalFiniteMean
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

/-! The compact directing limit has exactly the finite laws of the original
exchangeable Gram array. All sampling and approximation inputs are actual. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace OverlapPaper
set_option maxHeartbeats 700000

theorem tendsto_finitePrefixGramSamplingMean {ρ : ProbabilityMeasure DSDirectingSpace}
    {ρn : ℕ→ProbabilityMeasure DSDirectingSpace} (hlim : Tendsto ρn atTop (𝓝 ρ))
    (k M : ℕ) (f : C(FiniteOverlapArray k,ℝ)) :
    Tendsto (fun n => finitePrefixGramSamplingMean (ρn n) k M f) atTop
      (𝓝 (finitePrefixGramSamplingMean ρ k M f)) := by
  simp_rw [finitePrefixGramSamplingMean_eq]
  exact tendsto_integral_finiteCoordinateSamplingMean k _ hlim

theorem finitePrefixGramSamplingMean_limit_error (ν : ProbabilityMeasure GramArray)
    (hν : WeaklyExchangeableOverlapLaw (ν.map Subtype.val))
    (ρ : ProbabilityMeasure DSDirectingSpace) (φ : ℕ→ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (gramEmpiricalDirectingLaw ν∘φ) atTop (𝓝 ρ))
    (k M : ℕ) (f : C(FiniteOverlapArray k,ℝ)) (K : ℝ≥0) (hK : LipschitzWith K f) :
    |finitePrefixGramSamplingMean ρ k M f-
      (∫R,f (finiteOverlapPrefix k R.1) ∂(ν : Measure GramArray))|≤
      (K:ℝ)*(Fintype.card (FiniteReplicaPair k):ℝ)*Real.sqrt (1/((M+1:ℕ):ℝ)) := by
  let D := (K:ℝ)*(Fintype.card (FiniteReplicaPair k):ℝ)
  let C := ‖BoundedContinuousFunction.mkOfCompact f‖
  let B := ∫R,f (finiteOverlapPrefix k R.1) ∂(ν : Measure GramArray)
  have hzero : Tendsto (fun n => (1:ℝ)/(φ n+1:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hc : Tendsto (fun n => uniformSamplingCollisionRate (φ n+1) k) atTop (𝓝 0) := by
    simpa only [uniformSamplingCollisionRate,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,one_mul,mul_zero] using
      hzero.const_mul (k.choose 2 : ℝ)
  have hr : Tendsto (fun n => D*Real.sqrt (1/((M+1:ℕ):ℝ)+1/(φ n+1:ℝ))+
      2*C*uniformSamplingCollisionRate (φ n+1) k) atTop
      (𝓝 (D*Real.sqrt (1/((M+1:ℕ):ℝ)))) := by
    simpa only [add_zero,mul_zero] using
      ((tendsto_const_nhds (x := 1/((M+1:ℕ):ℝ))).add hzero).sqrt.const_mul D |>.add (hc.const_mul (2*C))
  have hl := ((tendsto_finitePrefixGramSamplingMean hlim k M f).sub_const B).abs
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_ge_atTop k] with n hn
  have hkn : k≤φ n+1 := (hn.trans (hφ.id_le n)).trans (Nat.le_succ _)
  have ha := finiteGramSamplingMean_prefix_bound (gramEmpiricalDirectingLaw ν (φ n)) k M f K hK
  have he := coordinatePairTailEnergy_empirical_bound ν (φ n) M
  have hb := finiteGramSamplingMean_empirical_collision_bound ν hν hkn f
  have hd : 0≤D := mul_nonneg K.2 (Nat.cast_nonneg _)
  calc
    _ ≤ |finitePrefixGramSamplingMean (gramEmpiricalDirectingLaw ν (φ n)) k M f-
          finiteGramSamplingMean (gramEmpiricalDirectingLaw ν (φ n)) k f|+
        |finiteGramSamplingMean (gramEmpiricalDirectingLaw ν (φ n)) k f-B| := abs_sub_le _ _ _
    _ ≤ D*Real.sqrt (coordinatePairTailEnergy (gramEmpiricalDirectingLaw ν (φ n)) M)+
        2*C*uniformSamplingCollisionRate (φ n+1) k := by
      exact add_le_add (by simpa only [abs_sub_comm,D] using ha) hb
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) hd) le_rfl

theorem finiteGramSamplingMean_limit_eq (ν : ProbabilityMeasure GramArray)
    (hν : WeaklyExchangeableOverlapLaw (ν.map Subtype.val))
    (ρ : ProbabilityMeasure DSDirectingSpace) (φ : ℕ→ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (gramEmpiricalDirectingLaw ν∘φ) atTop (𝓝 ρ))
    (k : ℕ) (f : C(FiniteOverlapArray k,ℝ)) (K : ℝ≥0) (hK : LipschitzWith K f) :
    finiteGramSamplingMean ρ k f=∫R,f (finiteOverlapPrefix k R.1) ∂(ν : Measure GramArray) := by
  let D := (K:ℝ)*(Fintype.card (FiniteReplicaPair k):ℝ)
  let B := ∫R,f (finiteOverlapPrefix k R.1) ∂(ν : Measure GramArray)
  have h1 := (tendsto_coordinatePairTailEnergy_zero ν ρ φ hφ hlim).sqrt.const_mul D
  have h2 : Tendsto (fun M : ℕ => D*Real.sqrt (1/((M+1:ℕ):ℝ))) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,Real.sqrt_zero,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt.const_mul D
  have hr : Tendsto (fun M => D*Real.sqrt (coordinatePairTailEnergy ρ M)+
      D*Real.sqrt (1/((M+1:ℕ):ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero,add_zero] using h1.add h2
  have hh : |finiteGramSamplingMean ρ k f-B|≤0 := ge_of_tendsto' hr (fun M => by
    calc
      _ ≤ |finiteGramSamplingMean ρ k f-finitePrefixGramSamplingMean ρ k M f|+
          |finitePrefixGramSamplingMean ρ k M f-B| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (finiteGramSamplingMean_prefix_bound ρ k M f K hK)
        (finitePrefixGramSamplingMean_limit_error ν hν ρ φ hφ hlim k M f K hK))
  exact sub_eq_zero.mp ((abs_nonpos_iff).mp hh)

def finiteGramSamplingProbability (ρ : ProbabilityMeasure DSDirectingSpace) (k : ℕ) :
    ProbabilityMeasure (FiniteOverlapArray k) :=
  ⟨(coordinateFiniteSamplingLaw ρ k).map (fun p => finiteCoordinateOverlap k p.2),
    (Measure.isProbabilityMeasure_map_iff
      ((measurable_finiteCoordinateOverlap k).comp measurable_snd).aemeasurable).mpr inferInstance⟩

theorem finiteGramSamplingProbability_eq (ν : ProbabilityMeasure GramArray)
    (hν : WeaklyExchangeableOverlapLaw (ν.map Subtype.val))
    (ρ : ProbabilityMeasure DSDirectingSpace) (φ : ℕ→ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (gramEmpiricalDirectingLaw ν∘φ) atTop (𝓝 ρ)) (k : ℕ) :
    finiteGramSamplingProbability ρ k=ν.map (fun R => finiteOverlapPrefix k R.1) := by
  have ht : Tendsto (fun _ : ℕ => finiteGramSamplingProbability ρ k) atTop
      (𝓝 (ν.map (fun R => finiteOverlapPrefix k R.1))) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f _hf hLip
    obtain ⟨K,hK⟩ := hLip
    let g : C(FiniteOverlapArray k,ℝ) := ⟨f,hK.continuous⟩
    have he := finiteGramSamplingMean_limit_eq ν hν ρ φ hφ hlim k g K hK
    have hi : (∫a,f a ∂(finiteGramSamplingProbability ρ k : Measure _))=
        ∫R,f (finiteOverlapPrefix k R.1) ∂(ν : Measure GramArray) := by
      change (∫a,f a ∂(coordinateFiniteSamplingLaw ρ k).map
        (fun p => finiteCoordinateOverlap k p.2))=_
      rw [integral_map (φ := fun p : DSDirectingSpace×(Fin k→DSCoordinateBall) =>
        finiteCoordinateOverlap k p.2) (f := f)
        ((measurable_finiteCoordinateOverlap k).comp measurable_snd).aemeasurable
          hK.continuous.measurable.aestronglyMeasurable]
      exact he
    have hj : (∫a,f a ∂(ν.map (fun R => finiteOverlapPrefix k R.1) : Measure _))=
        ∫R,f (finiteOverlapPrefix k R.1) ∂(ν : Measure GramArray) :=
      integral_map ((continuous_finiteOverlapPrefix k).comp continuous_subtype_val).measurable.aemeasurable
        hK.continuous.measurable.aestronglyMeasurable
    rw [hi,hj]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds ht

end OverlapPaper
