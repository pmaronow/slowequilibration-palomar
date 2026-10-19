module

public import SphericalAging.ShiftedPredictable
public import SphericalAging.VectorIto

public section

/-! Actual full-filtration Itô time-translation commutation. The operator
identity is proved on real adapted Brownian increments and extended to
all predictable L² integrands by genuine elementary density. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedIto
open HardSphereDynamics VectorIto ShiftedPredictable
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

lemma elementary_future (s a b : ℝ≥0) (Z : lpMeas ℝ ℝ (F a) 2 P) :
    elementaryPredictable F a b Z-FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s (elementaryPredictable F a b Z)=
      elementaryPredictable F (max a s) b (adaptedMono F (le_max_left a s) Z) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (elementaryPredictable F a b Z : TimeProcessL2 P)
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s (elementaryPredictable F a b Z)),
    elementaryPredictable_coeFn F a b Z,
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F s (elementaryPredictable F a b Z),
    elementaryPredictable_coeFn F (max a s) b (adaptedMono F (le_max_left a s) Z)]
    with q hsub hU hcut hR
  simp only [Submodule.coe_sub]
  rw [hsub,Pi.sub_apply,hcut,hR]
  by_cases hs : q ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame (W := Ω) s
  · rw [indicator_of_mem hs,sub_self]
    have hno : q.1 ∉ Ioc (max a s) b := fun h =>
      (not_lt_of_ge hs.1.2) ((le_max_right a s).trans_lt h.1)
    simp only [hno,ite_false]
  · rw [indicator_of_notMem hs,sub_zero,hU]
    have he : q.1 ∈ Ioc a b ↔ q.1 ∈ Ioc (max a s) b := by
      constructor
      · intro h
        have hslt : s < q.1 := by
          by_contra hle
          exact hs ⟨⟨(zero_le : 0 ≤ a).trans_lt h.1,le_of_not_gt hle⟩,mem_univ _⟩
        exact ⟨max_lt h.1 hslt,h.2⟩
      · intro h
        exact ⟨(le_max_left a s).trans_lt h.1,h.2⟩
    simp only [he]
    rfl

lemma coordinateIto_shift_elementary (D : BrownianDriver N P F) (i : Fin N)
    (s : ℝ≥0) {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (F a) 2 P) :
    coordinateIto (ShiftedBrownian.driver D s) i (predictableShift s (elementaryPredictable F a b Z))=
      coordinateIto D i (elementaryPredictable F a b Z-
        FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s (elementaryPredictable F a b Z)) := by
  rw [predictableShift_elementary,elementary_future]
  by_cases hbs : b ≤ s
  · rw [FourPapersCommon.FilteredBrownian.elementaryPredictable_eq_zero_of_le (ShiftedBrownian.filtration F s)
      (by simpa [tsub_eq_zero_of_le hbs] using (zero_le : (0 : ℝ≥0) ≤ a-s)),
      FourPapersCommon.FilteredBrownian.elementaryPredictable_eq_zero_of_le F (hbs.trans (le_max_right a s)),map_zero,map_zero]
  · have hsb : s ≤ b := (lt_of_not_ge hbs).le
    have hmax : max a s ≤ b := max_le hab hsb
    unfold coordinateIto
    rw [FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable _ _ _ (tsub_le_tsub_right hab s),
      FourPapersCommon.FilteredBrownian.naturalItoIntegral_elementaryPredictable _ _ _ hmax]
    apply Lp.ext
    filter_upwards [FourPapersCommon.FilteredBrownian.coeFn_elementaryBrownianValue
      ((ShiftedBrownian.driver D s).filtered i).toIsPreBrownianReal
      ((ShiftedBrownian.driver D s).coordinateStronglyMeasurable i)
      ((ShiftedBrownian.driver D s).filtered i) (tsub_le_tsub_right hab s) (adaptedShift s a Z),
      FourPapersCommon.FilteredBrownian.coeFn_elementaryBrownianValue (D.filtered i).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable i) (D.filtered i) hmax (adaptedMono F (le_max_left a s) Z)]
      with omega hL hR
    rw [hL,hR]
    simp only [ShiftedBrownian.driver_coordinate,add_tsub_cancel_of_le hsb,add_tsub_eq_max]
    change ((Z : RandomL2 P) omega)*
      ((D.coordinate i b omega-D.coordinate i s omega)-
        (D.coordinate i (max s a) omega-D.coordinate i s omega))=
      ((Z : RandomL2 P) omega)*(D.coordinate i b omega-D.coordinate i (max a s) omega)
    rw [max_comm s a]
    ring

/-- Exact Itô time-translation identity for every genuine predictable
L² integrand. The old integral retains precisely its future time slice. -/
theorem coordinateIto_predictableShift (D : BrownianDriver N P F) (i : Fin N)
    (s : ℝ≥0) (U : PredictableProcessL2 F P) :
    coordinateIto (ShiftedBrownian.driver D s) i (predictableShift s U)=
      coordinateIto D i (U-FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s U) := by
  let L := (coordinateIto (ShiftedBrownian.driver D s) i).comp (predictableShift s)
  let R := (coordinateIto D i).comp
    (ContinuousLinearMap.id ℝ (PredictableProcessL2 F P)-FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM F s)
  change L U=R U
  refine (FourPapersCommon.FilteredBrownian.denseRange_elementaryFinsuppToPredictable (P := P) F).induction_on U
    (isClosed_eq L.continuous R.continuous) ?_
  intro v
  have he (x : FourPapersCommon.FilteredBrownian.ElementaryPredictableIndex F P) :
      L (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x)=R (FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x) :=
    coordinateIto_shift_elementary D i s x.2.1.2 x.2.2
  have hv : FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable F P v=
      ∑ x ∈ v.support,v x • FourPapersCommon.FilteredBrownian.elementaryPredictableGenerator F P x := by
    simp only [FourPapersCommon.FilteredBrownian.elementaryFinsuppToPredictable,Finsupp.linearCombination_apply,Finsupp.sum]
  rw [hv,map_sum,map_sum]
  simp only [map_smul]
  exact Finset.sum_congr rfl (fun x _ => congrArg (fun Y => v x • Y) (he x))

end SphericalAging.ShiftedIto
