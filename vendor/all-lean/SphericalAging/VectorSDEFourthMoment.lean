module

public import SphericalAging.RandomVectorSDESecondMoment
public import SphericalAging.SharpScalarSecondMoment

public section

/-! Actual matrix SDE fourth moments with whole-vector constants.
The exponent is linear in the drift norm and in the true noise trace. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.VectorSDEFourthMoment
open HardSphereDynamics PredictableDriftTime RadialUniqueness VectorIto
  LinearSDEFourthMoment AffineSDEFourthMoment VectorSDESecondMoment SharpScalarSecondMoment
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Cauchy–Schwarz bounds the radial quadratic variation using the full
matrix trace, with no coordinate-count loss. -/
theorem vector_radial_noise_trace (x : State N) (b : Fin N → Fin N → ℝ) (S : ℝ≥0)
    (hb : (∑ i : Fin N,∑ j : Fin N,(b i j)^2) ≤ (S : ℝ)*‖x‖^2) :
    (∑ j : Fin N,(∑ i : Fin N,2*x i*b i j)^2) ≤ 4*(S : ℝ)*‖x‖^4 := by
  have hcol (j : Fin N) : (∑ i : Fin N,2*x i*b i j)^2 ≤
      4*‖x‖^2*(∑ i : Fin N,(b i j)^2) := by
    let v : State N := WithLp.toLp 2 (fun i => b i j)
    have hi : (∑ i : Fin N,2*x i*b i j)=2*inner ℝ x v := by
      simp only [v,PiLp.inner_apply,RCLike.inner_apply,PiLp.toLp_apply,starRingEnd_apply,star_trivial]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hv : (∑ i : Fin N,(b i j)^2)=‖v‖^2 := by
      simpa only [v,PiLp.toLp_apply,real_inner_self_eq_norm_sq] using coordinate_square_sum v
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℝ) x v) 2
    simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hh
    rw [hi,hv]
    nlinarith
  calc
    _ ≤ ∑ j : Fin N,4*‖x‖^2*(∑ i : Fin N,(b i j)^2) := Finset.sum_le_sum (fun j _ => hcol j)
    _ = 4*‖x‖^2*(∑ i : Fin N,∑ j : Fin N,(b i j)^2) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ 4*‖x‖^2*((S : ℝ)*‖x‖^2) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem bounded_randomInitial_vector_fourthMoment (D : BrownianDriver N P F)
    (Y : ℝ≥0 → Ω → State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀ ω, Continuous (fun t => Y t ω)) (R Kb Ks forcingBound driftBound noiseTraceBound : ℝ≥0)
    (hYbound : ∀ t ω, ‖Y t ω‖ ≤ R) (T : ℝ≥0) (Z0 : Ω → State N) (hZ0 : MemLp Z0 4 P)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : Fin N → ℝ≥0 → Ω → ℝ)
    (hA : ∀ i, (A i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => μ i q.1 q.2)
    (hμ : ∀ i, Measurable (Function.uncurry (μ i)))
    (hμint : ∀ i t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ i s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hAb : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖WithLp.toLp 2 (fun i => (A i : TimeProcessL2 P) q)‖ ≤
        driftBound*‖Y q.1 q.2‖+forcingBound)
    (hUtrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      (∑ i : Fin N,∑ j : Fin N,((U i j : TimeProcessL2 P) q)^2) ≤
        noiseTraceBound*‖Y q.1 q.2‖^2)
    (hUb : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖ ≤ Ks*‖Y q.1 q.2‖)
    (hUsupport : ∀ i j,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      q.1 ∉ Ioc 0 T → (U i j : TimeProcessL2 P) q=0)
    (hinitial : ∀ᵐ ω ∂P, Y 0 ω = Z0 ω)
    (heq : ∀ i t, SpherePreservation.coordinates Y i t =ᵐ[P] fun ω =>
      SpherePreservation.coordinates Y i 0 ω + integratedDrift (μ i) t ω + vectorProcess D (U i) t ω)
    (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, ‖Y t ω‖^4 ∂P) ≤ (∫ ω,((forcingBound : ℝ)^2+‖Z0 ω‖^2)^2 ∂P) * Real.exp
      (((4*driftBound+2+6*noiseTraceBound) : ℝ)*(t : ℝ)) := by
  let X := SpherePreservation.coordinates Y
  have hXa := SpherePreservation.coordinates_adapted hYa
  have hXc := SpherePreservation.coordinates_continuous (P := P) hYc
  have hXbound := SpherePreservation.coordinates_bound hYbound
  let S : ℝ≥0 := Ks*R
  have hUbound : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, ‖(U i j : ℝ≥0 × Ω → ℝ) q‖ ≤ S := by
    intro i j
    filter_upwards [hUb i j] with q hq
    exact hq.trans (mul_le_mul_of_nonneg_left (hYbound q.1 q.2) Ks.coe_nonneg)
  let B := RadialProcess.radialDrift A U X hXa hXc R hXbound S hUbound T
  let V := RadialProcess.radialNoise U X hXa hXc R hXbound T
  let Z : ℝ≥0 → Ω → ℝ := fun s ω => (forcingBound : ℝ)^2+‖Y s ω‖^2
  have hZa : StronglyAdapted F Z := fun s => ((hYa s).norm.pow 2).const_add _
  have hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω) := .of_forall (fun ω => ((hYc ω).norm.pow 2).const_add _)
  have hZbound : ∀ t ω, ‖Z t ω‖ ≤ (forcingBound^2+R^2 : ℝ≥0) := by
    intro t ω
    dsimp [Z]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (hYbound t ω) 2]
  have hUs := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hUb i))
  have hB : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(B : TimeProcessL2 P) q‖ ≤ ((2*driftBound+1+noiseTraceBound) : ℝ)*‖Z q.1 q.2‖ := by
    filter_upwards [RadialProcess.radialDrift_coe A U X hXa hXc R hXbound S hUbound T,hAb,hUtrace]
      with q hb ha hu
    intro hq
    rw [hb]
    have hcut (i : Fin N) :
        FourPapersCommon.continuousAdaptedTimeCut (RadialItoRepresentation.twiceState (X i)) T q = 2*(Y q.1 q.2) i := by
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
        RadialItoRepresentation.twiceState,X,SpherePreservation.coordinates]
    simp_rw [hcut]
    have hh := vector_radial_drift_bound (Y q.1 q.2) (fun i => (A i : TimeProcessL2 P) q)
      (fun i j => (U i j : TimeProcessL2 P) q) driftBound noiseTraceBound forcingBound ha hu
    change ‖_‖ ≤ ((2*driftBound+1+noiseTraceBound) : ℝ)*‖(forcingBound : ℝ)^2+‖Y q.1 q.2‖^2‖
    rw [Real.norm_of_nonneg (show 0 ≤ (forcingBound : ℝ)^2+‖Y q.1 q.2‖^2 by positivity)]
    exact hh
  have hZe : ∀ s, s ≤ T → ∀ᵐ ω ∂P, Z s ω = (forcingBound : ℝ)^2+‖Z0 ω‖^2 + driftVersion B s s ω +
      (vectorProcessLp D V s : Ω → ℝ) ω := by
    intro s hs
    have h := RadialProcess.quadratic_class_equation D A U X μ hXa hXc R hXbound S hUbound
      T s hs hA hμ hμint heq
    filter_upwards [h,hinitial] with ω hω h0
    have hsum (u : ℝ≥0) : (∑ i : Fin N,X i u ω^2)=‖Y u ω‖^2 := by
      simpa only [X,SpherePreservation.coordinates,real_inner_self_eq_norm_sq] using coordinate_square_sum (Y u ω)
    rw [hsum s,hsum 0,h0] at hω
    dsimp only [Z]
    linarith
  have hBsupport : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∉ Ioc 0 T →
      (B : TimeProcessL2 P) q=0 := by
    have hus := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hUsupport i))
    filter_upwards [RadialProcess.radialDrift_coe A U X hXa hXc R hXbound S hUbound T,hus]
      with q hb hu
    intro hq
    rw [hb]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false,zero_mul,Finset.sum_const_zero,zero_add]
    simp_rw [hu _ _ hq,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero]
  have hVtrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1 ∈ Ioc 0 T →
      (∑ j : Fin N,((V j : TimeProcessL2 P) q)^2) ≤
        ((4*noiseTraceBound : ℝ≥0) : ℝ)*(Z q.1 q.2)^2 := by
    have hv := ae_all_iff.mpr (fun j => RadialProcess.radialNoise_coe U X hXa hXc R hXbound T j)
    filter_upwards [hv,hUtrace] with q hv hu
    intro hq
    have he (j : Fin N) : (V j : TimeProcessL2 P) q=∑ i : Fin N,2*(Y q.1 q.2) i*(U i j : TimeProcessL2 P) q := by
      rw [hv j]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
        RadialItoRepresentation.twiceState,X,SpherePreservation.coordinates]
    simp_rw [he]
    have hh := vector_radial_noise_trace (Y q.1 q.2) (fun i j => (U i j : TimeProcessL2 P) q) noiseTraceBound hu
    refine hh.trans ?_
    have hz : ‖Y q.1 q.2‖^2 ≤ Z q.1 q.2 := by dsimp [Z];nlinarith [sq_nonneg (forcingBound : ℝ)]
    have hz0 : 0 ≤ Z q.1 q.2 := by dsimp [Z];positivity
    have hpow := pow_le_pow_left₀ (sq_nonneg ‖Y q.1 q.2‖) hz 2
    simp only [NNReal.coe_mul,NNReal.coe_ofNat]
    convert mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*(noiseTraceBound : ℝ) by positivity) using 1 <;> ring
  have hVbound : ∀ j,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(V j : TimeProcessL2 P) q‖ ≤ (radialNoiseConstant N Ks*R^2 : ℝ≥0) := by
    intro j
    filter_upwards [RadialProcess.radialNoise_coe U X hXa hXc R hXbound T j,hUs] with q hv hu
    simp only [NNReal.coe_mul,NNReal.coe_pow]
    rw [hv]
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
        RadialItoRepresentation.twiceState,X,SpherePreservation.coordinates]
      exact (radial_noise_bound (Y q.1 q.2) (fun i => (U i j : TimeProcessL2 P) q) Ks (fun i => hu i j)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hYbound q.1 q.2) 2) (by positivity))
    · simp [FourPapersCommon.continuousAdaptedTimeCut,hq]
      positivity
  have hz0 : MemLp (fun ω => (forcingBound : ℝ)^2+‖Z0 ω‖^2) 2 P := by
    have hh : MemLp (fun ω => ‖Z0 ω‖^2) 2 P := by
      apply (memLp_two_iff_integrable_sq (hZ0.aestronglyMeasurable.norm.pow 2)).mpr
      simpa only [Pi.pow_apply,← pow_mul,show 2*2=4 from rfl] using hZ0.integrable_norm_pow' 
    exact (memLp_const ((forcingBound : ℝ)^2)).add hh
  have h := scalar_equation_randomInitial_secondMoment D Z hZa hZc (forcingBound^2+R^2)
    (2*driftBound+1+noiseTraceBound) (4*noiseTraceBound) (radialNoiseConstant N Ks*R^2)
    hZbound T (fun ω => (forcingBound : ℝ)^2+‖Z0 ω‖^2) hz0 B V hBsupport hB hVtrace hVbound hZe t ht
  have hr : (2*(2*driftBound+1+noiseTraceBound)+4*noiseTraceBound : ℝ≥0)=
      (4*driftBound+2+6*noiseTraceBound : ℝ≥0) := by ring
  rw [hr] at h
  refine (show (∫ ω,‖Y t ω‖^4 ∂P) ≤ meanSquare (P := P) Z t from ?_).trans h
  have hm : MemLp (Y t) 4 P := MemLp.of_bound
    ((hYa t).mono (F.le t)).aestronglyMeasurable R (.of_forall (hYbound t))
  apply integral_mono_ae
  · simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hm.integrable_norm_rpow'
  · exact (bounded_memLp Z hZa (forcingBound^2+R^2) (.of_forall (fun ω s => hZbound s ω)) t).integrable_sq
  · exact .of_forall (fun ω => by
      dsimp [Z]
      nlinarith [sq_nonneg (forcingBound : ℝ),sq_nonneg ‖Y t ω‖,
        mul_nonneg (sq_nonneg (forcingBound : ℝ)) (sq_nonneg ‖Y t ω‖)])

theorem bounded_vector_fourthMoment (D : BrownianDriver N P F)
    (Y : ℝ≥0 → Ω → State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀ ω, Continuous (fun t => Y t ω)) (R Kb Ks forcingBound driftBound noiseTraceBound : ℝ≥0)
    (hYbound : ∀ t ω, ‖Y t ω‖ ≤ R) (T : ℝ≥0) (v0 : State N)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : Fin N → ℝ≥0 → Ω → ℝ)
    (hA : ∀ i, (A i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => μ i q.1 q.2)
    (hμ : ∀ i, Measurable (Function.uncurry (μ i)))
    (hμint : ∀ i t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ i s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hAb : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖WithLp.toLp 2 (fun i => (A i : TimeProcessL2 P) q)‖ ≤
        driftBound*‖Y q.1 q.2‖+forcingBound)
    (hUtrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      (∑ i : Fin N,∑ j : Fin N,((U i j : TimeProcessL2 P) q)^2) ≤
        noiseTraceBound*‖Y q.1 q.2‖^2)
    (hUb : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖ ≤ Ks*‖Y q.1 q.2‖)
    (hUsupport : ∀ i j,∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      q.1 ∉ Ioc 0 T → (U i j : TimeProcessL2 P) q=0)
    (hinitial : ∀ᵐ ω ∂P, Y 0 ω = v0)
    (heq : ∀ i t, SpherePreservation.coordinates Y i t =ᵐ[P] fun ω =>
      SpherePreservation.coordinates Y i 0 ω + integratedDrift (μ i) t ω + vectorProcess D (U i) t ω)
    (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, ‖Y t ω‖^4 ∂P) ≤ ((forcingBound : ℝ)^2+‖v0‖^2)^2 * Real.exp
      (((4*driftBound+2+6*noiseTraceBound) : ℝ)*(t : ℝ)) := by
  simpa only [integral_const,probReal_univ,one_smul] using
    bounded_randomInitial_vector_fourthMoment D Y hYa hYc R Kb Ks forcingBound driftBound noiseTraceBound
      hYbound T (fun _ => v0) (memLp_const v0) A U μ hA hμ hμint hAb hUtrace hUb
      hUsupport hinitial heq t ht

end SphericalAging.VectorSDEFourthMoment
