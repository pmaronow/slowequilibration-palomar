module

public import SphericalAging.LocalWeightedQuadratic

public section

/-! Mixed weighted brackets of the actual SDE coordinates, obtained by
polarization of genuine predictable Itô rows. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.SDEWeightedCovariation
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open VectorIto VectorItoFormula VectorQuadraticVariation WeightedVectorQuadratic LocalWeightedQuadratic
open AnnealedSDECore
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma driftVersion_add_ae (A B : PredictableProcessL2 F P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,∀ s,driftVersion (A+B) T s ω=driftVersion A T s ω+driftVersion B T s ω := by
  filter_upwards [driftVersion_sub_ae (A+B) B T] with ω hω
  intro s
  have h := hω s
  rw [add_sub_cancel_right] at h
  linarith

lemma vectorProcess_add_ae (D : BrownianDriver N P F)
    (U V : Fin N → PredictableProcessL2 F P) (s : ℝ≥0) :
    vectorProcess D (fun j => U j+V j) s =ᵐ[P]
      fun ω => vectorProcess D U s ω+vectorProcess D V s ω := by
  have hall := ae_all_iff.mpr (fun j : Fin N =>
    FilteredQuadraticVariation.naturalItoProcessRepresentative_add_ae
      (D.filtered j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j)
      (D.filtered j) (U j) (V j) s)
  filter_upwards [hall] with ω hω
  simp only [vectorProcess,coordinateProcess,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => (hω j).symm)

/-- A scalar prefix of the genuine predictable drift/Itô representation has
the actual weighted diffusion bracket. The representation is an integral
equation, not a supplied bracket or generator conclusion. -/
theorem prefix_weightedQuadratic_tendsto (D : BrownianDriver N P F)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (T t : ℝ≥0) (ht : t ≤ T) (W H : ℝ≥0 → Ω → ℝ) (z0 : Ω → ℝ)
    (sigma : Fin N → ℝ≥0 → Ω → ℝ)
    (hprefix : ∀ s,s ≤ T → W s =ᵐ[P]
      fun ω => z0 ω+driftVersion A T s ω+vectorProcess D U s ω)
    (hU : ∀ j,(U j : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma j) T)
    (hH : ∀ s,AEStronglyMeasurable (H s) P)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) :
    TendstoInMeasure P (fun n => weightedQuadraticSum H W t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*(∑ j : Fin N,sigma j s ω^2)
        ∂nonnegativeLebesgueMeasure) := by
  have hpred : (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
      (∑ j : Fin N,(U j : ℝ≥0 × Ω → ℝ) (s,ω)^2) ∂nonnegativeLebesgueMeasure) =ᵐ[P]
      fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*(∑ j : Fin N,sigma j s ω^2)
        ∂nonnegativeLebesgueMeasure := by
    have hrows := ae_all_iff.mpr hU
    have hswap := (Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae hrows
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hω,ae_restrict_mem measurableSet_Ioc] with s hs hst
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj := hs j
    dsimp only [Function.comp_def,Prod.swap] at hj
    simpa only [FourPapersCommon.continuousAdaptedTimeCut,
      ite_eq_left (show s ∈ Ioc (0 : ℝ≥0) T from ⟨hst.1,hst.2.trans ht⟩)] using congrArg (fun z : ℝ => z^2) hj
  apply (drift_ito_weightedQuadratic_tendsto D A U T t H hH hHc).congr
  · intro n
    have hgrid : ∀ᵐ ω ∂P,∀ k ∈ Finset.range (n+1),
        W (uniformPartitionTime t (n+1) k) ω = z0 ω+driftVersion A T (uniformPartitionTime t (n+1) k) ω+
          vectorProcess D U (uniformPartitionTime t (n+1) k) ω ∧
        W (uniformPartitionTime t (n+1) (k+1)) ω = z0 ω+driftVersion A T (uniformPartitionTime t (n+1) (k+1)) ω+
          vectorProcess D U (uniformPartitionTime t (n+1) (k+1)) ω :=
      (Finset.range (n+1)).eventually_all.mpr (fun k hk =>
        (hprefix _ ((uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n)
          (Nat.le_of_lt (Finset.mem_range.mp hk))).2.trans ht)).and
        (hprefix _ ((uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n)
          (Nat.succ_le_of_lt (Finset.mem_range.mp hk))).2.trans ht)))
    filter_upwards [hgrid] with ω hω
    unfold weightedQuadraticSum
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [(hω k hk).1,(hω k hk).2]
    ring
  · exact hpred

/-- The sum of two actual strong coordinates has the sum of their physical
noise rows as its quadratic bracket density. -/
theorem strong_coordinate_add_weightedQuadratic_tendsto (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T) (t : ℝ≥0) (ht : t ≤ T)
    (i k : Fin N) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ s,AEStronglyMeasurable (H s) P)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) :
    TendstoInMeasure P (fun n => weightedQuadraticSum H (fun s ω => X s ω i+X s ω k) t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
        (∑ j : Fin N,(sigma ω i j (X s ω)+sigma ω k j (X s ω))^2) ∂nonnegativeLebesgueMeasure) := by
  obtain ⟨A,U,hA,hU,hEq⟩ := hX.2.2.2
  apply prefix_weightedQuadratic_tendsto D (A i+A k) (fun j => U i j+U k j) T t ht
    (fun s ω => X s ω i+X s ω k) H (fun ω => Z0 ω i+Z0 ω k)
    (fun j s ω => sigma ω i j (X s ω)+sigma ω k j (X s ω))
  · intro s hs
    filter_upwards [hEq s hs i,hEq s hs k,
      driftVersion_eq_actual (A i) (fun r ω => b ω i (X r ω)) T (hA i),
      driftVersion_eq_actual (A k) (fun r ω => b ω k (X r ω)) T (hA k),
      vectorProcessLp_ae_eq D (U i) s,vectorProcessLp_ae_eq D (U k) s,
      driftVersion_add_ae (A i) (A k) T,vectorProcess_add_ae D (U i) (U k) s]
      with ω hi hk hdi hdk hui huk hd hu
    rw [hd s,hu,← hui,← huk, hdi s hs,hdk s hs]
    rw [hi,hk]
    ring
  · intro j
    filter_upwards [hU i j,hU k j,Lp.coeFn_add (U i j).val (U k j).val] with q hi hk ha
    have ha' : ((U i j+U k j : PredictableProcessL2 F P) : TimeProcessL2 P) q = (U i j : TimeProcessL2 P) q+(U k j : TimeProcessL2 P) q := by
      simpa only [Submodule.coe_add,Pi.add_apply] using ha
    rw [ha',hi,hk]
    simp only [FourPapersCommon.continuousAdaptedTimeCut]
    split_ifs <;> simp
  · exact hH
  · exact hHc

@[expose] def weightedCovariationSum (H X Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range n,H (uniformPartitionTime t n l) ω*
    (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)*
    (Y (uniformPartitionTime t n (l+1)) ω-Y (uniformPartitionTime t n l) ω)

/-- Every mixed coordinate bracket of an actual strong SDE has the true
physical covariance density, under continuous physical coefficients. -/
theorem strong_coordinate_weightedCovariation_tendsto (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T)
    (hsigma : ∀ ω i j,Continuous (sigma ω i j)) (t : ℝ≥0) (ht : t ≤ T)
    (i k : Fin N) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ s,AEStronglyMeasurable (H s) P)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) :
    TendstoInMeasure P (fun n => weightedCovariationSum H (fun s ω => X s ω i)
      (fun s ω => X s ω k) t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
        (∑ j : Fin N,sigma ω i j (X s ω)*sigma ω k j (X s ω)) ∂nonnegativeLebesgueMeasure) := by
  have ha := strong_coordinate_add_weightedQuadratic_tendsto D T hX t ht i k H hH hHc
  have hi := strong_coordinate_weightedQuadratic_tendsto D T hX t ht i H hH hHc
  have hk := strong_coordinate_weightedQuadratic_tendsto D T hX t ht k H hH hHc
  apply (((ha.sub_real_noMeas hi).sub_real_noMeas hk).const_mul_real_noMeas (1/2 : ℝ)).congr
  · intro n
    exact .of_forall (fun ω => by
      unfold weightedCovariationSum weightedQuadraticSum
      simp only [Finset.sum_sub_distrib,Finset.mul_sum]
      rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring)
  · filter_upwards [hX.2.2.1,hHc] with ω hxc hhc
    have hc (a : Fin N) (j : Fin N) : Continuous (fun s => sigma ω a j (X s ω)) :=
      (hsigma ω a j).comp hxc
    have hint (g : ℝ≥0 → ℝ) (hg : Continuous g) :
        IntegrableOn g (Ioc (0 : ℝ≥0) t) nonnegativeLebesgueMeasure :=
      (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hia := hint _ (hhc.mul (continuous_finsetSum Finset.univ (fun j _ => ((hc i j).add (hc k j)).pow 2)))
    have hii := hint _ (hhc.mul (continuous_finsetSum Finset.univ (fun j _ => (hc i j).pow 2)))
    have hik := hint _ (hhc.mul (continuous_finsetSum Finset.univ (fun j _ => (hc k j).pow 2)))
    simp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply] at hia hii hik
    have hfirst := integral_sub hia hii
    have hsecond := integral_sub (hia.sub hii) hik
    simp only [Pi.mul_apply,Pi.sub_apply] at hfirst hsecond
    rw [← hfirst,← hsecond,← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring)

end SphericalAging.SDEWeightedCovariation
