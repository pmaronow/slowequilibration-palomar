module

public import SphericalAging.StaticSDEOperators
public import SphericalAging.VectorZeroUniqueness

public section

/-! Pathwise uniqueness for actual bounded-state random-coefficient SDEs,
localized by an actual bounded random variable known at time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SphericalAging.RandomCoefficientUniqueness
open HardSphereDynamics PredictableDriftTime AnnealedSDECore BoundedItoMultiplier
open StaticSDEOperators VectorZeroUniqueness
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual strong solutions with the same random initial condition agree
where a bounded time-zero localizer is nonzero, provided the evaluated
coefficients satisfy the stated local Lipschitz comparisons. The actual
stochastic energy and Grönwall argument is proved. -/
theorem localized_strongSolutions_eq (D : BrownianDriver N P F)
    (b : Ω → Fin N → State N → ℝ) (sigma : Ω → Fin N → Fin N → State N → ℝ)
    (Z₀ : Ω → State N) (X Y : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z₀ X T)
    (hY : IsRandomStrongSolutionOn D b sigma Z₀ Y T)
    (L : ℝ≥0) (hXb : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖X t ω‖ ≤ L)
    (hYb : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖Y t ω‖ ≤ L)
    (C : Ω → ℝ) (hC : StronglyMeasurable[F 0] C) (Kc M K : ℝ≥0)
    (hCb : ∀ ω, ‖C ω‖ ≤ Kc)
    (hb : ∀ᵐ ω ∂P, C ω ≠ 0 → ∀ t, t ≤ T → ∀ i,
      ‖b ω i (X t ω) - b ω i (Y t ω)‖ ≤ (M : ℝ) * ‖X t ω - Y t ω‖)
    (hsigma : ∀ᵐ ω ∂P, C ω ≠ 0 → ∀ t, t ≤ T → ∀ i j,
      ‖sigma ω i j (X t ω) - sigma ω i j (Y t ω)‖ ≤ (K : ℝ) * ‖X t ω - Y t ω‖) :
    ∀ᵐ ω ∂P, C ω ≠ 0 → ∀ t, t ≤ T → X t ω = Y t ω := by
  obtain ⟨hZ₀,hXa,hXc,AX,UX,hAX,hUX,hXe⟩ := hX
  obtain ⟨_,hYa,hYc,AY,UY,hAY,hUY,hYe⟩ := hY
  let Z : ℝ≥0 → Ω → State N := fun t ω => C ω • (X (min t T) ω - Y (min t T) ω)
  let A : Fin N → PredictableProcessL2 F P := fun i =>
    predictableMulCLM T hC Kc hCb (AX i - AY i)
  let U : Fin N → Fin N → PredictableProcessL2 F P := fun i j =>
    predictableMulCLM T hC Kc hCb (UX i j - UY i j)
  have hZa : StronglyAdapted F Z := by
    intro t
    exact (hC.mono (F.mono (show (0 : ℝ≥0) ≤ t from zero_le))).smul
      (((hXa (min t T)).mono (F.mono (min_le_left _ _))).sub
        ((hYa (min t T)).mono (F.mono (min_le_left _ _))))
  have hZc : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω) := by
    filter_upwards [hXc,hYc] with ω hxc hyc
    exact ((hxc.comp (continuous_id.min continuous_const)).sub
      (hyc.comp (continuous_id.min continuous_const))).const_smul (C ω)
  have hZb : ∀ᵐ ω ∂P, ∀ t, ‖Z t ω‖ ≤ (Kc * (L+L) : ℝ≥0) := by
    filter_upwards [hXb,hYb] with ω hx hy
    intro t
    dsimp only [Z]
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (hCb ω) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
        (add_le_add (hx _ (min_le_right _ _)) (hy _ (min_le_right _ _)))) Kc.coe_nonneg)
  have hA : ∀ i, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(A i : TimeProcessL2 P) q‖ ≤ (M : ℝ) * ‖Z q.1 q.2‖ := by
    intro i
    have hp := (Measure.quasiMeasurePreserving_snd
      (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hb
    filter_upwards [predictableMulCLM_coe T hC Kc hCb (AX i - AY i),
      Lp.coeFn_sub (AX i : TimeProcessL2 P) (AY i : TimeProcessL2 P), hAX i,hAY i,hp]
      with q hmul hsub hx hy hlip
    intro hq
    change ‖(predictableMulCLM T hC Kc hCb (AX i - AY i) : TimeProcessL2 P) q‖ ≤ _
    rw [hmul]
    change ((AX i - AY i : PredictableProcessL2 F P) : TimeProcessL2 P) q =
      (AX i : TimeProcessL2 P) q - (AY i : TimeProcessL2 P) q at hsub
    rw [hsub]
    simp only [elementaryRepresentative,ite_eq_left hq,Pi.sub_apply,hx,hy,
      FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hq,Z,min_eq_left hq.2,norm_smul,norm_mul]
    by_cases hc : C q.2 = 0
    · simp [hc]
    · have hh := hlip hc q.1 hq.2 i
      calc
        _ ≤ ‖C q.2‖ * ((M : ℝ) * ‖X q.1 q.2 - Y q.1 q.2‖) :=
          mul_le_mul_of_nonneg_left hh (norm_nonneg _)
        _ = _ := by ring
  have hU : ∀ i j, ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, q.1 ∈ Ioc 0 T →
      ‖(U i j : TimeProcessL2 P) q‖ ≤ (K : ℝ) * ‖Z q.1 q.2‖ := by
    intro i j
    have hp := (Measure.quasiMeasurePreserving_snd
      (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hsigma
    filter_upwards [predictableMulCLM_coe T hC Kc hCb (UX i j - UY i j),
      Lp.coeFn_sub (UX i j : TimeProcessL2 P) (UY i j : TimeProcessL2 P), hUX i j,hUY i j,hp]
      with q hmul hsub hx hy hlip
    intro hq
    change ‖(predictableMulCLM T hC Kc hCb (UX i j - UY i j) : TimeProcessL2 P) q‖ ≤ _
    rw [hmul]
    change ((UX i j - UY i j : PredictableProcessL2 F P) : TimeProcessL2 P) q =
      (UX i j : TimeProcessL2 P) q - (UY i j : TimeProcessL2 P) q at hsub
    rw [hsub]
    simp only [elementaryRepresentative,ite_eq_left hq,Pi.sub_apply,hx,hy,
      FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hq,Z,min_eq_left hq.2,norm_smul,norm_mul]
    by_cases hc : C q.2 = 0
    · simp [hc]
    · have hh := hlip hc q.1 hq.2 i j
      calc
        _ ≤ ‖C q.2‖ * ((K : ℝ) * ‖X q.1 q.2 - Y q.1 q.2‖) :=
          mul_le_mul_of_nonneg_left hh (norm_nonneg _)
        _ = _ := by ring
  have heq : ∀ t, t ≤ T → ∀ i, ∀ᵐ ω ∂P, Z t ω i = driftVersion (A i) t t ω +
      (VectorIto.vectorProcessLp D (U i) t : Ω → ℝ) ω := by
    intro t ht i
    have hvec : VectorIto.vectorProcessLp D (fun j => UX i j - UY i j) t =
        VectorIto.vectorProcessLp D (UX i) t - VectorIto.vectorProcessLp D (UY i) t :=
      vectorProcessLp_sub D _ _ t
    have hn := vectorProcessLp_mul_coe D T t ht hC Kc hCb (fun j => UX i j - UY i j)
    rw [hvec] at hn
    filter_upwards [hXe t ht i,hYe t ht i,
      driftVersion_mul_coe T t ht hC Kc hCb (AX i - AY i), driftVersion_sub_ae (AX i) (AY i) t,
      driftVersion_eq_actual_at (AX i) _ T t ht (hAX i),
      driftVersion_eq_actual_at (AY i) _ T t ht (hAY i),hn,
      Lp.coeFn_sub (VectorIto.vectorProcessLp D (UX i) t) (VectorIto.vectorProcessLp D (UY i) t)]
      with ω hx hy hmul hsub hax hay hn hns
    change (C ω • (X (min t T) ω - Y (min t T) ω)) i =
      driftVersion (predictableMulCLM T hC Kc hCb (AX i - AY i)) t t ω + _
    simp only [min_eq_left ht,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
    rw [hmul,hsub t,hax,hay,hn,hns]
    simp only [Pi.sub_apply]
    rw [hx,hy]
    ring
  have hz := bounded_vector_equation_zero D Z hZa hZc (Kc*(L+L)) M K hZb T A U hA hU heq
  filter_upwards [hz] with ω hω
  intro hc t ht
  have hzero : C ω • (X t ω - Y t ω) = 0 := by
    simpa only [Z,min_eq_left ht] using hω t ht
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hc)

end SphericalAging.RandomCoefficientUniqueness
