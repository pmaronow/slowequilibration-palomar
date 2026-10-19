module
public import Paper.ParisiSpatialSmooth
public import Paper.ParisiGradientMartingaleLaw
public import Paper.ParisiSelectedMoment
public import Paper.ParisiStateStability

@[expose] public section

/-! # Actual optimal state and spatial-derivative observables

These definitions use the literally constructed Parisi PDE solution and the
canonical Brownian pathwise integral solution at zero initial field.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace FRSB

abbrev ParisiMeasure := Paper.ParisiMeasure
abbrev Overlap := Paper.Overlap
abbrev BrownianSample := Paper.BrownianSample

def alpha (μ : ParisiMeasure) (s : ℝ) : ℝ := Paper.parisiCDF μ s

def parisiSpatialJet (β : ℝ) (μ : ParisiMeasure) (j : ℕ) (s x : ℝ) : ℝ :=
  if j = 0 then Paper.parisiPotential β μ (s, x) else
    Paper.parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1)
      (Paper.bcfSpatialDerivative (Paper.parisiGradientBCF β μ) (j - 1)) (s, x)

def optimalStateReal (β : ℝ) (μ : ParisiMeasure) (ω : BrownianSample) : ℝ → ℝ :=
  Paper.canonicalParisiStateReal β 0 μ (fun s x => Paper.parisiGradient β μ (s, x))
    (Paper.continuous_parisiGradient β μ)
    (fun s x => Paper.norm_parisiGradient_le_one β μ (s, x))
    (Paper.lipschitzWith_parisiGradient_all β μ) ω

def optimalState (β : ℝ) (μ : ParisiMeasure) (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  Paper.canonicalParisiItoState β 0 μ (fun s x => Paper.parisiGradient β μ (s, x))
    (Paper.continuous_parisiGradient β μ)
    (fun s x => Paper.norm_parisiGradient_le_one β μ (s, x))
    (Paper.lipschitzWith_parisiGradient_all β μ) t ω

def jetProcess (β : ℝ) (μ : ParisiMeasure) (j : ℕ) (s : ℝ) (ω : BrownianSample) : ℝ :=
  parisiSpatialJet β μ j s (optimalStateReal β μ ω s)

abbrev M (β : ℝ) (μ : ParisiMeasure) := jetProcess β μ 1
abbrev C (β : ℝ) (μ : ParisiMeasure) := jetProcess β μ 2
abbrev D (β : ℝ) (μ : ParisiMeasure) := jetProcess β μ 3
abbrev A (β : ℝ) (μ : ParisiMeasure) := jetProcess β μ 4

def Gamma (β : ℝ) (μ : ParisiMeasure) (s : ℝ) : ℝ :=
  ∫ ω, M β μ s ω ^ 2 ∂Paper.canonicalBrownianMeasure

@[simp] theorem parisiSpatialJet_one (β : ℝ) (μ : ParisiMeasure) (s x : ℝ) :
    parisiSpatialJet β μ 1 s x = Paper.parisiGradient β μ (s, x) := by
  simp only [parisiSpatialJet, show ¬(1 : ℕ) = 0 by omega, ite_false, Nat.sub_self,
    Paper.bcfSpatialDerivative, iteratedDeriv_zero]
  apply congrArg (fun v => Paper.parisiSlabExtend (by norm_num : (0 : ℝ) ≤ 1) v (s, x))
  ext p
  simp

theorem parisiSpatialJet_succ_eq_gradient_derivative (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (s x : ℝ) :
    parisiSpatialJet β μ (j + 1) s x =
      iteratedDeriv j (fun y => Paper.parisiGradient β μ (s,y)) x := by
  simp only [parisiSpatialJet, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel, Paper.parisiSlabExtend]
  rw [Paper.bcfSpatialDerivative_apply _ (Paper.contDiff_bcfTranslate_parisiGradient β μ)]
  rfl

/-- Positive jets are derivatives of the actual potential on the physical strip. -/
theorem parisiSpatialJet_eq_iteratedDeriv (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    parisiSpatialJet β μ j s x =
      iteratedDeriv j (fun y => Paper.parisiPotential β μ (s,y)) x := by
  cases j with
  | zero => simp [parisiSpatialJet]
  | succ j =>
    rw [parisiSpatialJet_succ_eq_gradient_derivative,
      Paper.iteratedDeriv_parisiPotential_eq_gradient β μ j s x hs]

/-- Every positive jet has a bounded, jointly continuous extension to all times. -/
theorem continuous_parisiSpatialJet_succ (β : ℝ) (μ : ParisiMeasure) (j : ℕ) :
    Continuous (fun p : ℝ × ℝ => parisiSpatialJet β μ (j+1) p.1 p.2) := by
  simp only [parisiSpatialJet, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel]
  exact Paper.continuous_parisiSlabExtend (by norm_num) _

theorem norm_parisiSpatialJet_succ_le (β : ℝ) (μ : ParisiMeasure) (j : ℕ) (s x : ℝ) :
    ‖parisiSpatialJet β μ (j+1) s x‖ ≤
      ‖Paper.bcfSpatialDerivative (Paper.parisiGradientBCF β μ) j‖ := by
  simp only [parisiSpatialJet, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel]
  exact Paper.norm_parisiSlabExtend_le (by norm_num) _ _

theorem hasDerivAt_parisiSpatialJet_succ (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (s x : ℝ) :
    HasDerivAt (fun y => parisiSpatialJet β μ (j+1) s y)
      (parisiSpatialJet β μ (j+2) s x) x := by
  simp_rw [parisiSpatialJet_succ_eq_gradient_derivative]
  have hd := (Paper.contDiff_parisiGradient_spatial β μ s).differentiable_iteratedDeriv j
    (by exact_mod_cast ENat.natCast_lt_top j) x
  simpa only [iteratedDeriv_succ] using hd.hasDerivAt

theorem hasDerivAt_parisiSpatialJet (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => parisiSpatialJet β μ j s y)
      (parisiSpatialJet β μ (j+1) s x) x := by
  cases j with
  | zero =>
    change HasDerivAt (fun y => Paper.parisiPotential β μ (s,y))
      (parisiSpatialJet β μ 1 s x) x
    rw [parisiSpatialJet_one]
    exact Paper.hasDerivAt_parisiPotential_spatial_all β μ s x hs
  | succ j => exact hasDerivAt_parisiSpatialJet_succ β μ j s x

@[simp] theorem optimalState_initial (β : ℝ) (μ : ParisiMeasure) (ω : BrownianSample) :
    optimalStateReal β μ ω 0 = 0 := Paper.canonicalParisiState_initial β 0 μ _ _ _ _ ω

theorem continuous_optimalStateReal (β : ℝ) (μ : ParisiMeasure) (ω : BrownianSample) :
    Continuous (optimalStateReal β μ ω) := Paper.continuous_canonicalParisiStateReal β 0 μ _ _ _ _ ω

theorem optimalState_integral_equation (β : ℝ) (μ : ParisiMeasure) (ω : BrownianSample)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    optimalStateReal β μ ω t = β * Paper.canonicalBrownian t.toNNReal ω +
      ∫ s in 0..t, β ^ 2 * alpha μ s * M β μ s ω := by
  simpa only [optimalStateReal, alpha, jetProcess, parisiSpatialJet_one, zero_add] using
    Paper.canonicalParisiState_integral_equation β 0 μ _ _ _ _ ω ht

theorem optimalState_eq_real (β : ℝ) (μ : ParisiMeasure) {t : ℝ≥0}
    (ht : (t : ℝ) ≤ 1) (ω : BrownianSample) :
    optimalState β μ t ω = optimalStateReal β μ ω t :=
  Paper.canonicalParisiItoState_eq β 0 μ _ _ _ _ ht ω

theorem optimalStateReal_eq_selected (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    optimalStateReal β μ = Paper.selectedParisiStateReal β 0 hβ μ := rfl

theorem optimalState_eq_selected (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    optimalState β μ = Paper.selectedParisiItoState β 0 hβ μ := rfl

theorem Gamma_eq_selectedSecondMoment (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (s : ℝ) :
    Gamma β μ s = Paper.selectedParisiSecondMoment β 0 hβ μ s := by
  simp only [Gamma, M, jetProcess, parisiSpatialJet_one]
  rfl

theorem continuousOn_Gamma (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ContinuousOn (Gamma β μ) (Icc (0 : ℝ) 1) := by
  convert Paper.continuousOn_selectedParisiSecondMoment β 0 hβ μ using 1
  funext s
  exact Gamma_eq_selectedSecondMoment β hβ μ s

/-- The actual zero-field magnetization is the checked general Parisi martingale. -/
theorem martingale_M (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Martingale (fun (t : Icc (0 : ℝ≥0) 1) ω => M β μ t.1 ω)
      (StochasticCalculus.monotoneReindexFiltration Paper.canonicalBrownianFiltration
        (fun t : Icc (0 : ℝ≥0) 1 => t.1) (fun _ _ h => h)) Paper.canonicalBrownianMeasure := by
  convert Paper.martingale_selectedParisiGradient β 0 hβ μ using 1
  funext t ω
  simp only [M, jetProcess, parisiSpatialJet_one, Paper.selectedParisiGradientProcess,
    ← optimalState_eq_selected β hβ μ,
    optimalState_eq_real β μ (NNReal.coe_le_coe.mpr t.property.2) ω]

end FRSB
