module

public import SphericalAging.MultivariateItoWeights
public import SphericalAging.LinearSDELocalization

public section

/-! Genuine C² multivariate Itô formula for the actual bounded physical
strong SDE. All stochastic integrands are constructed predictable L² classes
and identified with the physical derivative/noise evaluations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.MultivariateItoFormula
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open VectorIto VectorItoFormula WeightedItoSums WeightedDriftSums AnnealedSDECore
open MultivariateTaylor MultivariateTaylorPartition MultivariateItoSums MultivariateItoWeights SDEWeightedLinear
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual multivariate C² Itô formula. The compact derivative cutoff is
only an integrand construction; its equality with the true derivative is
proved on every physical path. No bracket, generator, or Itô conclusion is
assumed. -/
theorem strong_C2_ito_formula (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T)
    (hsigma : ∀ ω i j,Continuous (sigma ω i j)) (R : ℝ) (hR : 0<R)
    (hXb : ∀ᵐ ω ∂P,∀ s,‖X s ω‖≤R) {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ V : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i j,(V i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun s ω => fderiv ℝ f (X s ω) (basisVector i)*sigma ω i j (X s ω)) T) ∧
      ∀ᵐ ω ∂P,f (X T ω)=f (Z0 ω)+
        (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
          fderiv ℝ f (X s ω) (basisVector i)*b ω i (X s ω) ∂nonnegativeLebesgueMeasure)+
        (∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω)+
        (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
          Hessian f (X s ω) (basisVector i) (basisVector k)*
            (∑ j : Fin N,sigma ω i j (X s ω)*sigma ω k j (X s ω)) ∂nonnegativeLebesgueMeasure) := by
  obtain ⟨A,U,hA,hU,hEq⟩ := hX.2.2.2
  have hWa (i : Fin N) := weight_stronglyAdapted hf R hR i hX.2.1
  have hWc (i : Fin N) := weight_continuous hf R hR i hX.2.2.1
  choose K hK using (fun i : Fin N => derivativeWeight_bounded hf R hR i)
  let H (i : Fin N) : ℝ≥0 → Ω → ℝ := fun s ω => derivativeWeight f R hR i (X s ω)
  let V (i j : Fin N) : PredictableProcessL2 F P :=
    weightedIntegrand (H i) (hWa i) (hWc i) (K i) (fun s ω => hK i (X s ω)) T (U i j)
  have hV (i j : Fin N) : (V i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => FourPapersCommon.continuousAdaptedTimeCut (H i) T q*(U i j : TimeProcessL2 P) q := by
    exact predictableProduct_coe
      (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F (H i) (hWa i) (hWc i) T)
      (K i) (.of_forall (timeCut_bound (H i) (K i) (fun s ω => hK i (X s ω)) T)) (U i j)
  refine ⟨V,?_,?_⟩
  · intro i j
    have hb := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hXb
    filter_upwards [hV i j,hU i j,hb] with q hv hu hbq
    rw [hv,hu]
    simp only [FourPapersCommon.continuousAdaptedTimeCut]
    split_ifs
    · dsimp only [H]
      rw [derivativeWeight_eq f R hR i _ (hbq q.1)]
    · simp
  · have hpref (i : Fin N) (s : ℝ≥0) (hs : s≤T) :
        (fun ω => X s ω i)=ᵐ[P] fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω := by
      filter_upwards [hEq s hs i,driftVersion_eq_actual (A i)
        (fun r ω => b ω i (X r ω)) T (hA i),vectorProcessLp_ae_eq D (U i) s]
        with ω he hd hi
      rw [hd s hs,← hi]
      exact he
    have hlin (i : Fin N) := prefix_weightedLeftSum_tendsto D (A i) (U i) T T le_rfl
      (fun s ω => X s ω i) (H i) (fun ω => Z0 ω i) (hpref i) (hWa i) (hWc i) (K i)
      (fun s ω => hK i (X s ω))
    have hlin' (i : Fin N) : TendstoInMeasure P (fun n => weightedLeftSum (H i)
        (fun s ω => X s ω i) T (n+1)) atTop
        (fun ω => (∫ s in Ioc (0 : ℝ≥0) T,fderiv ℝ f (X s ω) (basisVector i)*
          b ω i (X s ω) ∂nonnegativeLebesgueMeasure)+(vectorIto D (V i) : Ω → ℝ) ω) := by
      apply (hlin i).congr_right
      filter_upwards [weighted_drift_eq_actual (A i) T T le_rfl (H i)
        (fun s ω => b ω i (X s ω)) (hA i),hXb] with ω hd hb
      rw [hd]
      congr 1
      apply integral_congr_ae
      exact .of_forall (fun s => by
        dsimp only [H]
        rw [derivativeWeight_eq f R hR i _ (hb s)])
    have hsum := tendstoInMeasure_finsetSum Finset.univ _ _ (fun i _ => hlin' i)
    have hlinear : TendstoInMeasure P (fun n => linearApprox f X T (n+1)) atTop
        (fun ω => (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
          fderiv ℝ f (X s ω) (basisVector i)*b ω i (X s ω) ∂nonnegativeLebesgueMeasure)+
          ∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω) := by
      apply hsum.congr
      · intro n
        exact (linearApprox_eq_weightedLeftSum f R hR X hXb T (n+1)).symm
      · exact .of_forall (fun ω => Finset.sum_add_distrib)
    have hquad := strong_quadratic_tendsto D T hX hsigma T le_rfl hf
    have hrem := strong_remainder_tendsto D T hX T le_rfl hf
    have htotal := (hlinear.add_real_noMeas hquad).add_real_noMeas hrem
    have hactual : TendstoInMeasure P
        (fun _ : ℕ => fun ω => f (X T ω)-f (X 0 ω)) atTop
        (fun ω => (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
          fderiv ℝ f (X s ω) (basisVector i)*b ω i (X s ω) ∂nonnegativeLebesgueMeasure)+
          (∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω)+
          (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
            Hessian f (X s ω) (basisVector i) (basisVector k)*
              (∑ j : Fin N,sigma ω i j (X s ω)*sigma ω k j (X s ω)) ∂nonnegativeLebesgueMeasure)) := by
      apply htotal.congr
      · intro n
        exact .of_forall (fun ω => (partition_identity f X T (n+1) (Nat.zero_lt_succ n) ω).symm)
      · exact .of_forall (fun _ => add_zero _)
    have hc : TendstoInMeasure P (fun _ : ℕ => fun ω => f (X T ω)-f (X 0 ω)) atTop
        (fun ω => f (X T ω)-f (X 0 ω)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => (hf.continuous.comp_aestronglyMeasurable
        (((hX.2.1 T).mono (F.le T)).aestronglyMeasurable)).sub
          (hf.continuous.comp_aestronglyMeasurable (((hX.2.1 0).mono (F.le 0)).aestronglyMeasurable)))
        (.of_forall (fun _ => tendsto_const_nhds))
    have hz : X 0=ᵐ[P] Z0 := by
      have hall := ae_all_iff.mpr (fun i : Fin N => hEq 0 bot_le i)
      have hi : ∀ᵐ ω ∂P,∀ i : Fin N,(vectorProcessLp D (U i) 0 : Ω → ℝ) ω=0 :=
        ae_all_iff.mpr (fun i => by
          rw [LinearSDELocalization.vectorProcessLp_zero_time]
          exact Lp.coeFn_zero ℝ 2 P)
      filter_upwards [hall,hi] with ω hω hiω
      apply PiLp.ext
      intro i
      have he := hω i
      simp only [NNReal.coe_zero,intervalIntegral.integral_same,add_zero,hiω i] at he
      exact he
    filter_upwards [tendstoInMeasure_ae_unique hc hactual,hz] with ω he hzω
    rw [hzω] at he
    linarith

end SphericalAging.MultivariateItoFormula
