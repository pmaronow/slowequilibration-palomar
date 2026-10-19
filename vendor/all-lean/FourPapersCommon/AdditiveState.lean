module
public import FourPapersCommon.IntegralDriftStability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

@[expose] public section

/-! The actual pathwise integral solution for a bounded measurable time
coefficient and bounded continuous spatially Lipschitz gradient. -/
noncomputable section
open Set Filter Function MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal
namespace FourPapersCommon
open Paper Paper.IntegralPicard

structure AdditiveDriftData where
  coefficient : ℝ → ℝ
  gradient : ℝ → ℝ → ℝ
  radius : ℝ≥0
  gradientLip : ℝ≥0
  coefficient_measurable : Measurable coefficient
  coefficient_bound : ∀ t, ‖coefficient t‖ ≤ radius
  gradient_continuous : Continuous (Function.uncurry gradient)
  gradient_bound : ∀ t x, ‖gradient t x‖ ≤ 1
  gradient_lipschitz : ∀ t, LipschitzWith gradientLip (gradient t)

def additiveNoiseDrift (d : AdditiveDriftData) (W : ℝ → ℝ) (t x : ℝ) : ℝ :=
  d.coefficient t*d.gradient t (x+W t)

theorem isBoundedMeasurableDrift_additiveNoiseDrift (d : AdditiveDriftData)
    (W : ℝ → ℝ) (hW : Continuous W) :
    IsBoundedMeasurableDrift (additiveNoiseDrift d W) d.radius (d.radius*d.gradientLip) := by
  constructor
  · exact (d.coefficient_measurable.comp measurable_fst).mul
      (d.gradient_continuous.measurable.comp
        (measurable_fst.prodMk (measurable_snd.add (hW.measurable.comp measurable_fst))))
  · intro t x
    change ‖d.coefficient t*d.gradient t (x+W t)‖ ≤ d.radius
    rw [norm_mul]
    calc
      _ ≤ (d.radius : ℝ)*1 := mul_le_mul (d.coefficient_bound t)
        (d.gradient_bound t _) (norm_nonneg _) d.radius.2
      _ = _ := mul_one _
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (d.coefficient t*d.gradient t (x+W t))
      (d.coefficient t*d.gradient t (y+W t)) ≤ (d.radius*d.gradientLip : ℝ≥0)*dist x y
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    have hb := (d.gradient_lipschitz t).dist_le_mul (x+W t) (y+W t)
    rw [dist_add_right, dist_eq_norm] at hb
    exact (mul_le_mul (d.coefficient_bound t) hb (norm_nonneg _) d.radius.2).trans_eq (by
      simp only [NNReal.coe_mul]; ring)

def additiveCorrection (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → ℝ) (hW : Continuous W) : Curve hT h d.radius :=
  solution hT (isBoundedMeasurableDrift_additiveNoiseDrift d W hW)

def additiveStateReal (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → ℝ) (hW : Continuous W) (t : ℝ) : ℝ :=
  (additiveCorrection d h T hT W hW).compProj t+W t

theorem continuous_additiveStateReal (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → ℝ) (hW : Continuous W) : Continuous (additiveStateReal d h T hT W hW) :=
  (ODE.FunSpace.continuous_compProj _).add hW

theorem additiveStateReal_integral_equation (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    additiveStateReal d h T hT W hW t = h+W t+
      ∫ s in 0..t, d.coefficient s*d.gradient s (additiveStateReal d h T hT W hW s) := by
  unfold additiveStateReal
  rw [ODE.FunSpace.compProj_of_mem ht]
  have he := solution_equation (h := h) hT
    (isBoundedMeasurableDrift_additiveNoiseDrift d W hW) ⟨t,ht⟩
  change (solution (h := h) hT _) ⟨t,ht⟩+W t = _
  rw [he]
  unfold additiveCorrection
  dsimp only [additiveNoiseDrift]
  ring

theorem additiveStateReal_initial (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → ℝ) (hW : Continuous W) (h0 : W 0 = 0) :
    additiveStateReal d h T hT W hW 0 = h := by
  simpa [h0] using additiveStateReal_integral_equation d h T hT W hW ⟨le_rfl,hT⟩

theorem additiveStateReal_unique (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    (W : ℝ → ℝ) (hW : Continuous W) (X : ℝ → ℝ) (hX : Continuous X)
    (hXe : ∀ t ∈ Icc (0 : ℝ) T, X t = h+W t+
      ∫ s in 0..t, d.coefficient s*d.gradient s (X s)) :
    EqOn X (additiveStateReal d h T hT W hW) (Icc (0 : ℝ) T) := by
  have he := real_solution_unique (h := h) hT
    (isBoundedMeasurableDrift_additiveNoiseDrift d W hW) (fun t => X t-W t) (hX.sub hW) (by
      intro t ht
      rw [hXe t ht]
      simp only [additiveNoiseDrift, sub_add_cancel]
      ring)
  intro t ht
  have hh := he t ht
  unfold additiveStateReal additiveCorrection
  linarith

theorem additiveStateReal_causal (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) (W Z : ℝ → ℝ)
    (hW : Continuous W) (hZ : Continuous Z) (hnoise : EqOn W Z (Icc (0 : ℝ) r)) :
    EqOn (additiveStateReal d h T hT W hW) (additiveStateReal d h T hT Z hZ) (Icc (0 : ℝ) r) := by
  have heW := additiveStateReal_unique d h r hr.1 W hW
    (additiveStateReal d h T hT W hW) (continuous_additiveStateReal d h T hT W hW)
    (fun t ht => additiveStateReal_integral_equation d h T hT W hW ⟨ht.1,ht.2.trans hr.2⟩)
  have heZ := additiveStateReal_unique d h r hr.1 W hW
    (additiveStateReal d h T hT Z hZ) (continuous_additiveStateReal d h T hT Z hZ) (by
      intro t ht
      have hh := additiveStateReal_integral_equation d h T hT Z hZ ⟨ht.1,ht.2.trans hr.2⟩
      rw [← hnoise ht] at hh
      exact hh)
  exact fun t ht => (heW ht).trans (heZ ht).symm

def additiveStatePath (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    (w : C(Icc (0 : ℝ) T,ℝ)) : C(Icc (0 : ℝ) T,ℝ) :=
  (additiveCorrection d h T hT (parisiNoiseExtension hT w)
    (continuous_parisiNoiseExtension hT w)).toContinuousMap+w

theorem additiveStatePath_apply (d : AdditiveDriftData) (h T : ℝ) (hT : 0 ≤ T)
    (w : C(Icc (0 : ℝ) T,ℝ)) (t : Icc (0 : ℝ) T) :
    additiveStatePath d h T hT w t = additiveStateReal d h T hT
      (parisiNoiseExtension hT w) (continuous_parisiNoiseExtension hT w) t := by
  simp [additiveStatePath, additiveStateReal, parisiNoiseExtension, projIcc_val]

end FourPapersCommon
