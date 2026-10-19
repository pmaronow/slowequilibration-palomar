module

public import SphericalAging.HamiltonianDisorderDerivative
public import SphericalAging.HamiltonianCoefficientDependence

public section

/-! True disorder derivatives of the nonlinear drift and noise classes.
The drift derivative includes the actual affine tensor forcing; its state
Jacobian and parameter cross error are controlled by genuine increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianDisorderCoefficientDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime HamiltonianPicardDependence GlobalHamiltonianParameter
open HamiltonianDisorderDerivative HamiltonianDisorderLinearization HamiltonianDisorderForcingOperator
open HamiltonianCoefficientDependence StochasticTaylorRemainder TerminalLinearity
open LinearSDETimeFourthMoment
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem hasFDerivAt_of_eventual_quadratic_error {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G) (L : E →L[ℝ] G) (x : E)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᶠ y in 𝓝 x,‖f y-f x-L (y-x)‖ ≤ C*‖y-x‖^2) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hevent : ∀ᶠ y : E in 𝓝 x,‖y-x‖ < ε/(C+1) := by
    exact Filter.mem_of_superset (Metric.ball_mem_nhds x (div_pos hε (by linarith : 0 < C+1)))
      (fun y hy => by simpa only [Metric.mem_ball,dist_eq_norm,Set.mem_ofPred_eq] using hy)
  filter_upwards [hevent,hbound] with y hy hb
  apply hb.trans
  have hh : C*‖y-x‖ ≤ ε := by
    have he := (lt_div_iff₀ (by linarith : 0 < C+1)).mp hy
    nlinarith [norm_nonneg (y-x)]
  nlinarith [norm_nonneg (y-x)]

@[expose]  def driftResponse (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i : Fin N) :
    FiniteModel.Disorder N p →L[ℝ] PredictableProcessL2 F P :=
  (coefficientOperator (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i)).comp
    (disorderResponse D β R hR J x T)+forcingOperator β R hR T (globalClass D β R hR T (J,x)) i

@[expose]  def noiseResponse (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i j : Fin N) :
    FiniteModel.Disorder N p →L[ℝ] PredictableProcessL2 F P :=
  (coefficientOperator (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i j)).comp
    (disorderResponse D β R hR J x T)

 theorem coefficient_responses_quadratic_bound (D₀ : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) :
    ∃ Cb Cs : ℝ,0 ≤ Cb ∧ 0 ≤ Cs ∧
      ∀ᶠ K : FiniteModel.Disorder N p in 𝓝 J,
      (∀ i,‖driftClass (NullAugmentation.driver D₀) β R hR T i (K,x)-
        driftClass (NullAugmentation.driver D₀) β R hR T i (J,x)-
        driftResponse (NullAugmentation.driver D₀) β R hR J x T i (K-J)‖ ≤ Cb*‖K-J‖^2) ∧
      (∀ i j,‖noiseClass (NullAugmentation.driver D₀) β R hR T i j (K,x)-
        noiseClass (NullAugmentation.driver D₀) β R hR T i j (J,x)-
        noiseResponse (NullAugmentation.driver D₀) β R hR J x T i j (K-J)‖ ≤ Cs*‖K-J‖^2) := by
  let D := NullAugmentation.driver D₀
  let A : ℝ≥0 := ‖J‖₊+1
  let jb : BoundedDisorder N p A := ⟨J,by simp [A]⟩
  let hj := drift_family_lipschitz β R hR A jb
  let hs := noise_family_lipschitz N R hR
  let X := GlobalSDE.horizonProcess D hj hs x T
  let U := hamiltonianClass D β R hR A T (jb,x)
  let ha := GlobalSDE.horizonProcess_stronglyAdapted D hj hs x T
  let hc := GlobalSDE.horizonProcess_continuous D hj hs x T
  let L := response D β R hR A jb x T
  obtain ⟨C,hC,hquad⟩ := HamiltonianDisorderDerivative.quadratic_error_bound D₀ β R hR A jb x T
  obtain ⟨Lb,hbd⟩ := HamiltonianFlowDerivative.cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := HamiltonianFlowDerivative.cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  obtain ⟨Kh,hKh⟩ := bounded_increment_norm (p := p) D β R hR A T
  let C4 := HamiltonianDisorderIncrement.fourthConstant (N := N) (p := p) β R hR A T
  let Crb := (Lb : ℝ)*Real.sqrt C4
  let Crs := (Ls : ℝ)*Real.sqrt C4
  let Cc := (∑ I : FiniteModel.TensorIndex N p,couplingConstant β R hR I : ℝ≥0)*(Kh : ℝ)
  let Cb := Crb+(driftBound (N := N) (p := p) β R hR A : ℝ)*C+Cc
  let Cs := Crs+(noiseBound N R hR : ℝ)*C
  refine ⟨Cb,Cs,by dsimp [Cb,Crb,Cc];positivity,by dsimp [Cs,Crs];positivity,?_⟩
  have hevent : ∀ᶠ K : FiniteModel.Disorder N p in 𝓝 J,‖K-J‖ < 1 := by
    exact Filter.mem_of_superset (Metric.ball_mem_nhds J zero_lt_one)
      (fun K hK => by simpa only [Metric.mem_ball,dist_eq_norm,Set.mem_ofPred_eq] using hK)
  filter_upwards [hevent] with K hK
  have hKA : ‖K‖ ≤ A := by
    change ‖K‖ ≤ ‖J‖+1
    have hn : ‖K‖ ≤ ‖K-J‖+‖J‖ := by simpa only [sub_add_cancel] using norm_add_le (K-J) J
    linarith
  let kb : BoundedDisorder N p A := ⟨K,hKA⟩
  let hk := drift_family_lipschitz β R hR A kb
  let Y := GlobalSDE.horizonProcess D hk hs x T
  let V := hamiltonianClass D β R hR A T (kb,x)
  have h4 := HamiltonianDisorderIncrement.increment_fourthMoment D₀ β R hR A jb kb x T
  have hi : Integrable (fun q => ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4) (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [stateTimeCut_eq_indicator,HamiltonianDisorderIncrement.increment,AffineSecantDifference.difference] using
      h4.1.integrable_norm_pow (by norm_num)
  have hm : (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤ C4*‖K-J‖^4 := by
    simpa only [stateTimeCut_eq_indicator,HamiltonianDisorderIncrement.increment,AffineSecantDifference.difference] using h4.2
  have hq : ‖V-U-L (K-J)‖ ≤ C*‖K-J‖^2 := hquad kb
  have hcross (i : Fin N) : ‖forcingOperator β R hR T V i (K-J)-forcingOperator β R hR T U i (K-J)‖ ≤ Cc*‖K-J‖^2 := by
    calc
      _ ≤ (∑ I : FiniteModel.TensorIndex N p,couplingConstant β R hR I : ℝ≥0)*‖K-J‖*‖V-U‖ :=
        forcingOperator_state_sub_bound β R hR T U V i (K-J)
      _ ≤ (∑ I : FiniteModel.TensorIndex N p,couplingConstant β R hR I : ℝ≥0)*‖K-J‖*((Kh : ℝ)*‖K-J‖) :=
        mul_le_mul_of_nonneg_left (hKh jb kb x) (by positivity)
      _ = _ := by dsimp [Cc];ring
  have hglobal : globalClass D β R hR T (J,x)=U := globalClass_eq_bounded D β R hR A T J jb.2 x
  constructor
  · intro i
    let a := HamiltonianDisorderLinearization.driftRows D β R hR A jb x T i
    let r := remainder ha hc (cutoffDrift_contDiff β J R hR i) (hj i) T U V
    have hr : ‖r‖ ≤ Crb*‖K-J‖^2 := norm_remainder_le_parameter ha hc
      (GlobalSDE.horizonProcess_timeCut D hj hs x T) (GlobalSDE.horizonProcess_timeCut D hk hs x T)
      (cutoffDrift_contDiff β J R hR i) (hj i) (hbd i) hi _
      (HamiltonianDisorderIncrement.fourthConstant_nonneg β R hR A T) (K-J) hm
    rw [driftClass_eq_bounded D β R hR A T i K hKA x,driftClass_eq_bounded D β R hR A T i J jb.2 x]
    change ‖predictableCoefficient (hk i) V T-predictableCoefficient (hj i) U T-
      (driftResponse D β R hR J x T i) (K-J)‖ ≤ _
    simp only [driftResponse,add_apply,ContinuousLinearMap.comp_apply,coefficientOperator_apply,hglobal]
    change ‖predictableCoefficient (hk i) V T-predictableCoefficient (hj i) U T-
      (apply a (L (K-J))+forcingOperator β R hR T U i (K-J))‖ ≤ _
    have hp := coefficient_drift_affine_difference β J K R hR hj hk T V i
    have he : predictableCoefficient (hk i) V T-predictableCoefficient (hj i) U T-
        (apply a (L (K-J))+forcingOperator β R hR T U i (K-J)) =
        r+apply a (V-U-L (K-J))+(forcingOperator β R hR T V i (K-J)-forcingOperator β R hR T U i (K-J)) := by
      dsimp [r,a,HamiltonianDisorderLinearization.driftRows,StochasticFlowDerivative.driftRows]
      simp only [remainder,apply_sub]
      rw [sub_eq_iff_eq_add] at hp
      rw [hp]
      abel
    rw [he]
    calc
      _ ≤ ‖r‖+‖apply a (V-U-L (K-J))‖+‖forcingOperator β R hR T V i (K-J)-forcingOperator β R hR T U i (K-J)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ Crb*‖K-J‖^2+(driftBound (N := N) (p := p) β R hR A : ℝ)*(C*‖K-J‖^2)+Cc*‖K-J‖^2 :=
        add_le_add (add_le_add hr ((norm_apply_le a _).trans (mul_le_mul_of_nonneg_left hq (by positivity)))) (hcross i)
      _ = _ := by dsimp [Cb];ring
  · intro i j
    let a := HamiltonianDisorderLinearization.noiseRows D β R hR A jb x T i j
    let r := remainder ha hc (cutoffNoise_contDiff R hR i j) (hs i j) T U V
    have hr : ‖r‖ ≤ Crs*‖K-J‖^2 := norm_remainder_le_parameter ha hc
      (GlobalSDE.horizonProcess_timeCut D hj hs x T) (GlobalSDE.horizonProcess_timeCut D hk hs x T)
      (cutoffNoise_contDiff R hR i j) (hs i j) (hsd i j) hi _
      (HamiltonianDisorderIncrement.fourthConstant_nonneg β R hR A T) (K-J) hm
    simp only [noiseClass,globalClass_eq_bounded D β R hR A T K hKA x,hglobal,noiseResponse,
      ContinuousLinearMap.comp_apply,coefficientOperator_apply]
    change ‖predictableCoefficient (hs i j) V T-predictableCoefficient (hs i j) U T-apply a (L (K-J))‖ ≤ _
    have he : predictableCoefficient (hs i j) V T-predictableCoefficient (hs i j) U T-apply a (L (K-J)) =
        r+apply a (V-U-L (K-J)) := by
      dsimp [r,a,HamiltonianDisorderLinearization.noiseRows,StochasticFlowDerivative.noiseRows]
      simp only [remainder,apply_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖r‖+‖apply a (V-U-L (K-J))‖ := norm_add_le _ _
      _ ≤ Crs*‖K-J‖^2+(noiseBound N R hR : ℝ)*(C*‖K-J‖^2) :=
        add_le_add hr ((norm_apply_le a _).trans (mul_le_mul_of_nonneg_left hq (by positivity)))
      _ = _ := by dsimp [Cs];ring

 theorem driftClass_hasFDerivAt_disorder (D₀ : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i : Fin N) :
    HasFDerivAt (fun K : FiniteModel.Disorder N p => driftClass (NullAugmentation.driver D₀) β R hR T i (K,x))
      (driftResponse (NullAugmentation.driver D₀) β R hR J x T i) J := by
  obtain ⟨Cb,Cs,hb,hs,hq⟩ := coefficient_responses_quadratic_bound D₀ β R hR J x T
  exact hasFDerivAt_of_eventual_quadratic_error _ _ J Cb hb (hq.mono (fun K h => h.1 i))

 theorem noiseClass_hasFDerivAt_disorder (D₀ : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i j : Fin N) :
    HasFDerivAt (fun K : FiniteModel.Disorder N p => noiseClass (NullAugmentation.driver D₀) β R hR T i j (K,x))
      (noiseResponse (NullAugmentation.driver D₀) β R hR J x T i j) J := by
  obtain ⟨Cb,Cs,hb,hs,hq⟩ := coefficient_responses_quadratic_bound D₀ β R hR J x T
  exact hasFDerivAt_of_eventual_quadratic_error _ _ J Cs hs (hq.mono (fun K h => h.2 i j))
end SphericalAging.HamiltonianDisorderCoefficientDerivative
