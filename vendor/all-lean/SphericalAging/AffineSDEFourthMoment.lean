module

public import SphericalAging.InhomogeneousLinearSDE

public section

/-! Genuine fourth moments with bounded predictable drift forcing. The
extra deterministic radial coordinate is B²; all estimates remain uniform
in the localization radius and vanish quartically as the forcing vanishes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AffineSDEFourthMoment
open HardSphereDynamics PredictableDriftTime RadialUniqueness VectorIto LinearSDEFourthMoment
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def affineRadialDriftConstant (N : ℕ) (Kb Ks : ℝ≥0) : ℝ≥0 := 2*N*Kb+N+N^2*Ks^2

/-- True radial drift bound for bounded affine rows. -/
theorem radial_drift_bound_affine (x : State N) (a : Fin N → ℝ) (b : Fin N → Fin N → ℝ)
    (Kb Ks B : ℝ≥0) (ha : ∀ i, ‖a i‖ ≤ Kb*‖x‖+B)
    (hb : ∀ i j, ‖b i j‖ ≤ Ks*‖x‖) :
    ‖(∑ i,2*x i*a i)+(∑ i,∑ j,(b i j)^2)‖ ≤
      (affineRadialDriftConstant N Kb Ks : ℝ)*((B : ℝ)^2+‖x‖^2) := by
  have hfirst : ‖∑ i,2*x i*a i‖ ≤ (N : ℝ)*(2*Kb*‖x‖^2+‖x‖^2+(B : ℝ)^2) := by
    calc
      _ ≤ ∑ i : Fin N,‖2*x i*a i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N,(2*(Kb : ℝ)*‖x‖^2+‖x‖^2+(B : ℝ)^2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,norm_mul]
        have hm := mul_le_mul (PiLp.norm_apply_le x i) (ha i) (norm_nonneg _) (norm_nonneg _)
        rw [show ‖(2 : ℝ)‖=2 by norm_num]
        nlinarith [hm,sq_nonneg (‖x‖-(B : ℝ))]
      _ = _ := by simp;ring
  have hsecond : ‖∑ i,∑ j,(b i j)^2‖ ≤ (N : ℝ)^2*(Ks : ℝ)^2*‖x‖^2 := by
    calc
      _ ≤ ∑ i : Fin N,‖∑ j : Fin N,(b i j)^2‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N,∑ _j : Fin N,(Ks : ℝ)^2*‖x‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro j _
        simpa only [norm_pow,mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb i j) 2
      _ = _ := by simp;ring
  refine (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans ?_)
  simp only [affineRadialDriftConstant,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_pow,
    NNReal.coe_ofNat,NNReal.coe_natCast]
  have hN : (0 : ℝ) ≤ N := by positivity
  have hKb : (0 : ℝ) ≤ Kb := Kb.coe_nonneg
  have hs : 0 ≤ (N : ℝ)^2*(Ks : ℝ)^2 := by positivity
  nlinarith [mul_nonneg (show 0 ≤ 2*(N : ℝ)*Kb by positivity) (sq_nonneg (B : ℝ)),
    mul_nonneg hs (sq_nonneg (B : ℝ))]

/-- Genuine fourth-moment bound for a bounded actual matrix SDE. The
radial integral equation is derived by the proved norm-squared Itô theorem.
The constant does not depend on the stopping radius. -/
theorem bounded_affine_fourthMoment (D : BrownianDriver N P F)
    (Y : ℝ≥0 → Ω → State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀ ω, Continuous (fun t => Y t ω)) (R Kb Ks forcingBound : ℝ≥0)
    (hYbound : ∀ t ω, ‖Y t ω‖ ≤ R) (T : ℝ≥0) (v0 : State N)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : Fin N → ℝ≥0 → Ω → ℝ)
    (hA : ∀ i, (A i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => μ i q.1 q.2)
    (hμ : ∀ i, Measurable (Function.uncurry (μ i)))
    (hμint : ∀ i t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ i s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (hAb : ∀ i, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(A i : TimeProcessL2 P) q‖ ≤ Kb*‖Y q.1 q.2‖+forcingBound)
    (hUb : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖ ≤ Ks*‖Y q.1 q.2‖)
    (hinitial : ∀ᵐ ω ∂P, Y 0 ω = v0)
    (heq : ∀ i t, SpherePreservation.coordinates Y i t =ᵐ[P] fun ω =>
      SpherePreservation.coordinates Y i 0 ω + integratedDrift (μ i) t ω + vectorProcess D (U i) t ω)
    (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, ‖Y t ω‖^4 ∂P) ≤ 3*((forcingBound : ℝ)^2+‖v0‖^2)^2 * Real.exp
      ((3*(T : ℝ)*(affineRadialDriftConstant N Kb Ks : ℝ)^2+
        3*N*(radialNoiseConstant N Ks : ℝ)^2)*(t : ℝ)) := by
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
  have hZbound : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ (forcingBound^2+R^2 : ℝ≥0) := .of_forall (fun ω t => by
    dsimp [Z]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (hYbound t ω) 2])
  have hAs := ae_all_iff.mpr hAb
  have hUs := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hUb i))
  have hB : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(B : TimeProcessL2 P) q‖ ≤ (affineRadialDriftConstant N Kb Ks : ℝ)*‖Z q.1 q.2‖ := by
    filter_upwards [RadialProcess.radialDrift_coe A U X hXa hXc R hXbound S hUbound T,hAs,hUs]
      with q hb ha hu
    intro hq
    rw [hb]
    have hcut (i : Fin N) :
        FourPapersCommon.continuousAdaptedTimeCut (RadialItoRepresentation.twiceState (X i)) T q = 2*(Y q.1 q.2) i := by
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
        RadialItoRepresentation.twiceState,X,SpherePreservation.coordinates]
    simp_rw [hcut]
    have hh := radial_drift_bound_affine (Y q.1 q.2) (fun i => (A i : TimeProcessL2 P) q)
      (fun i j => (U i j : TimeProcessL2 P) q) Kb Ks forcingBound ha hu
    change ‖_‖ ≤ (affineRadialDriftConstant N Kb Ks : ℝ)*‖(forcingBound : ℝ)^2+‖Y q.1 q.2‖^2‖
    rw [Real.norm_of_nonneg (show 0 ≤ (forcingBound : ℝ)^2+‖Y q.1 q.2‖^2 by positivity)]
    exact hh
  have hV : ∀ j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(V j : TimeProcessL2 P) q‖ ≤ (radialNoiseConstant N Ks : ℝ)*‖Z q.1 q.2‖ := by
    intro j
    filter_upwards [RadialProcess.radialNoise_coe U X hXa hXc R hXbound T j,hUs] with q hv hu
    intro hq
    rw [hv]
    have hcut (i : Fin N) :
        FourPapersCommon.continuousAdaptedTimeCut (RadialItoRepresentation.twiceState (X i)) T q = 2*(Y q.1 q.2) i := by
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,
        RadialItoRepresentation.twiceState,X,SpherePreservation.coordinates]
    simp_rw [hcut]
    have hh := radial_noise_bound (Y q.1 q.2) (fun i => (U i j : TimeProcessL2 P) q) Ks (fun i => hu i j)
    change ‖_‖ ≤ (radialNoiseConstant N Ks : ℝ)*‖(forcingBound : ℝ)^2+‖Y q.1 q.2‖^2‖
    rw [Real.norm_of_nonneg (show 0 ≤ (forcingBound : ℝ)^2+‖Y q.1 q.2‖^2 by positivity)]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (sq_nonneg (forcingBound : ℝ))) (by positivity))
  have hZe : ∀ s, s ≤ T → ∀ᵐ ω ∂P, Z s ω = (forcingBound : ℝ)^2+‖v0‖^2 + driftVersion B s s ω +
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
  have h := nonzero_linear_equation_secondMoment D Z hZa hZc (forcingBound^2+R^2)
    (affineRadialDriftConstant N Kb Ks) (radialNoiseConstant N Ks) hZbound T
    ((forcingBound : ℝ)^2+‖v0‖^2) B V hB hV hZe t ht
  refine (show (∫ ω,‖Y t ω‖^4 ∂P) ≤ meanSquare (P := P) Z t from ?_).trans h
  have hm : MemLp (Y t) 4 P := MemLp.of_bound
    ((hYa t).mono (F.le t)).aestronglyMeasurable R (.of_forall (hYbound t))
  apply integral_mono_ae
  · simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hm.integrable_norm_rpow'
  · exact (bounded_memLp Z hZa (forcingBound^2+R^2) hZbound t).integrable_sq
  · exact .of_forall (fun ω => by
      dsimp [Z]
      nlinarith [sq_nonneg (forcingBound : ℝ),sq_nonneg ‖Y t ω‖,
        mul_nonneg (sq_nonneg (forcingBound : ℝ)) (sq_nonneg ‖Y t ω‖)])

end SphericalAging.AffineSDEFourthMoment
