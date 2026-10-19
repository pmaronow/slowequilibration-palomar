module
public import FRSB.ConstantMassIto

@[expose] public section

/-! Endpoint closure of the actual weighted constant-mass backward identity.
Continuity and uniform boundedness pass through the stochastic expectation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper StochasticCalculus
open scoped Topology NNReal
namespace FRSB

theorem selectedParisiItoState_constantMass_weighted
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (a T : ℝ≥0) (hT : 0 < T)
    (haT : (a : ℝ) + T ≤ 1) (m : ℝ)
    (hcdf : ∀ s ∈ Ico (a : ℝ) ((a : ℝ) + T), parisiCDF μ s = m)
    (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ) (L L1 : ℝ) (hL : 0 ≤ L) (hL1 : 0 ≤ L1)
    (hψb : ∀ x, |ψ x| ≤ L) (hψd : ∀ x, |deriv ψ x| ≤ L1)
    (Z : BrownianSample → ℝ) (hZ : StronglyMeasurable[canonicalBrownianFiltration a] Z)
    (C : ℝ≥0) (hC : ∀ sample : BrownianSample, ‖Z sample‖ ≤ C) :
    (∫ ω, Z ω * ψ (selectedParisiItoState β h hβ μ (a + T) ω) ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * parisiBackwardQuotient β μ ((a : ℝ) + T) m ψ (β ^ 2 * (T : ℝ))
        (selectedParisiItoState β h hβ μ a ω) ∂canonicalBrownianMeasure := by
  let b : ℝ := (a : ℝ) + T
  have hab : (a : ℝ) < b := by dsimp [b]; exact lt_add_of_pos_right _ (NNReal.coe_pos.mpr hT)
  have hbb : b ∈ Icc (0 : ℝ) 1 := ⟨by positivity, haT⟩
  have hm : m ∈ Icc (0 : ℝ) 1 := by
    have he := hcdf (a : ℝ) ⟨le_rfl, hab⟩
    rw [← he]
    exact ⟨parisiCDF_nonneg μ a, parisiCDF_le_one μ a⟩
  have hD := heatC2Datum_exp_parisiPotential β μ b m hbb hm
  change HeatC2Datum (parisiHeatWeight β μ b m) at hD
  have hN := hD.mul hψ
  have hp := fun v x => (gaussianHeatFlow_parisiHeatWeight_pos β μ b m v x hbb).ne'
  have hQ := (continuous_backwardHeatQuotient_jets hN hD hp).1
  change Continuous (fun p : ℝ × ℝ => parisiBackwardQuotient β μ b m ψ p.1 p.2) at hQ
  let S := selectedParisiItoState β h hβ μ
  have hSm (t : ℝ≥0) : StronglyMeasurable (S t) :=
    (stronglyAdapted_canonicalParisiItoState β h μ (fun t x => parisiGradient β μ (t, x))
      (continuous_parisiGradient β μ) (fun t x => norm_parisiGradient_le_one β μ (t, x))
      (lipschitzWith_parisiGradient β hβ μ) t).mono (canonicalBrownianFiltration.le t)
  have hSc (ω : BrownianSample) : Continuous (fun t => S t ω) :=
    continuous_canonicalParisiItoState β h μ (fun t x => parisiGradient β μ (t, x))
      (continuous_parisiGradient β μ) (fun t x => norm_parisiGradient_le_one β μ (t, x))
      (lipschitzWith_parisiGradient β hβ μ) ω
  let E : ℝ≥0 → ℝ := fun c => ∫ ω, Z ω *
    parisiBackwardQuotient β μ b m ψ (β ^ 2 * (b - a - c)) (S (a + c) ω)
      ∂canonicalBrownianMeasure
  let R : ℝ := ∫ ω, Z ω * parisiBackwardQuotient β μ b m ψ (β ^ 2 * (b - a))
    (S a ω) ∂canonicalBrownianMeasure
  have hE : Continuous E := by
    apply continuous_of_dominated (bound := fun _ => (C : ℝ) * L)
    · intro c
      exact ((hZ.mono (canonicalBrownianFiltration.le a)).mul
        (hQ.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk (hSm (a + c))))).aestronglyMeasurable
    · intro c
      filter_upwards [] with ω
      rw [norm_mul]
      exact mul_le_mul (hC ω)
        (by simpa only [Real.norm_eq_abs] using
          abs_parisiBackwardQuotient_le β μ b m hbb hm ψ hψ L hψb _ (S (a + c) ω))
        (norm_nonneg _) C.coe_nonneg
    · exact integrable_const _
    · filter_upwards [] with ω
      exact continuous_const.mul (hQ.comp
        ((by fun_prop : Continuous (fun c : ℝ≥0 => β ^ 2 * (b - a - c))).prodMk
          ((hSc ω).comp (continuous_const.add continuous_id))))
  have hclosed : IsClosed {c : ℝ≥0 | E c = R} := isClosed_eq hE continuous_const
  have hsub : Iio T ⊆ {c : ℝ≥0 | E c = R} := by
    intro c hc
    exact selectedParisiItoState_constantMass_weighted_interior β h hβ μ a c b m
      hab haT (by
        have hct : (c : ℝ) < (T : ℝ) := NNReal.coe_lt_coe.mpr hc
        dsimp [b]
        linarith) hm hcdf ψ hψ L L1 hL hL1 hψb hψd Z hZ C hC
  have hmem : T ∈ closure (Iio T) := by
    rw [closure_Iio' (show (Iio T).Nonempty from ⟨0, hT⟩)]
    exact show T ≤ T from le_rfl
  have he : E T = R := (closure_minimal hsub hclosed) hmem
  have hbT : b - a - T = 0 := by dsimp [b]; ring
  have hb0 : b - a = (T : ℝ) := by dsimp [b]; ring
  dsimp only [E] at he
  rw [hbT, mul_zero] at he
  have hz : parisiBackwardQuotient β μ b m ψ 0 = ψ :=
    funext (fun x => parisiBackwardQuotient_terminal β μ b m x ψ)
  rw [hz] at he
  simpa only [R, S, hb0, b] using he

theorem selectedParisiItoState_constantMass_weighted_cos
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (a T : ℝ≥0) (hT : 0 < T)
    (haT : (a : ℝ) + T ≤ 1) (m ξ : ℝ)
    (hcdf : ∀ s ∈ Ico (a : ℝ) ((a : ℝ) + T), parisiCDF μ s = m)
    (Z : BrownianSample → ℝ) (hZ : StronglyMeasurable[canonicalBrownianFiltration a] Z)
    (C : ℝ≥0) (hC : ∀ sample : BrownianSample, ‖Z sample‖ ≤ C) :
    (∫ ω, Z ω * Real.cos (ξ * selectedParisiItoState β h hβ μ (a + T) ω) ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * parisiBackwardQuotient β μ ((a : ℝ) + T) m (fun y => Real.cos (ξ * y))
        (β ^ 2 * (T : ℝ)) (selectedParisiItoState β h hβ μ a ω) ∂canonicalBrownianMeasure := by
  apply selectedParisiItoState_constantMass_weighted β h hβ μ a T hT haT m hcdf
    (fun y => Real.cos (ξ * y)) (heatC2Datum_cos ξ) 1 |ξ| zero_le_one (abs_nonneg ξ)
    (fun y => Real.abs_cos_le_one _) _ Z hZ C hC
  intro y
  have hd : deriv (fun z => Real.cos (ξ * z)) y = -Real.sin (ξ * y) * ξ := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id y).const_mul ξ).cos).deriv
  rw [hd, abs_mul, abs_neg]
  exact mul_le_of_le_one_left (abs_nonneg ξ) (Real.abs_sin_le_one _)

theorem selectedParisiItoState_constantMass_weighted_sin
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (a T : ℝ≥0) (hT : 0 < T)
    (haT : (a : ℝ) + T ≤ 1) (m ξ : ℝ)
    (hcdf : ∀ s ∈ Ico (a : ℝ) ((a : ℝ) + T), parisiCDF μ s = m)
    (Z : BrownianSample → ℝ) (hZ : StronglyMeasurable[canonicalBrownianFiltration a] Z)
    (C : ℝ≥0) (hC : ∀ sample : BrownianSample, ‖Z sample‖ ≤ C) :
    (∫ ω, Z ω * Real.sin (ξ * selectedParisiItoState β h hβ μ (a + T) ω) ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * parisiBackwardQuotient β μ ((a : ℝ) + T) m (fun y => Real.sin (ξ * y))
        (β ^ 2 * (T : ℝ)) (selectedParisiItoState β h hβ μ a ω) ∂canonicalBrownianMeasure := by
  apply selectedParisiItoState_constantMass_weighted β h hβ μ a T hT haT m hcdf
    (fun y => Real.sin (ξ * y)) (heatC2Datum_sin ξ) 1 |ξ| zero_le_one (abs_nonneg ξ)
    (fun y => Real.abs_sin_le_one _) _ Z hZ C hC
  intro y
  have hd : deriv (fun z => Real.sin (ξ * z)) y = Real.cos (ξ * y) * ξ := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id y).const_mul ξ).sin).deriv
  rw [hd, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg ξ) (Real.abs_cos_le_one _)

end FRSB
