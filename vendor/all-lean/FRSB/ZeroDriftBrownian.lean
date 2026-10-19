module
public import Paper.DiracShift

@[expose] public section

/-! Actual Brownian zero-drift states with deterministic initial position and
all original information retained at the deterministic starting time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped NNReal ENNReal
namespace FRSB

 def zeroDriftBrownian (β : ℝ) (a : ℝ≥0) (y : ℝ)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ := y+canonicalDiracShiftMartingale β a t ω

@[simp] theorem zeroDriftBrownian_initial (β : ℝ) (a : ℝ≥0) (y : ℝ)
    (ω : BrownianSample) : zeroDriftBrownian β a y 0 ω=y := by
  simp [zeroDriftBrownian,canonicalDiracShiftMartingale]

 theorem continuous_zeroDriftBrownian (β : ℝ) (a : ℝ≥0) (y : ℝ)
    (ω : BrownianSample) : Continuous (fun t => zeroDriftBrownian β a y t ω) := by
  unfold zeroDriftBrownian canonicalDiracShiftMartingale
  exact continuous_const.add (continuous_const.mul
    (((continuous_canonicalBrownian ω).comp (continuous_const.add continuous_id)).sub continuous_const))

 theorem stronglyAdapted_zeroDriftBrownian (β : ℝ) (a : ℝ≥0) (y : ℝ) :
    StronglyAdapted (canonicalBrownianShiftFiltration a) (zeroDriftBrownian β a y) :=
  fun t => stronglyMeasurable_const.add ((martingale_canonicalDiracShiftMartingale β a).stronglyAdapted t)

 theorem boundedDriftItoCharacteristics_zeroDriftBrownian (β : ℝ) (a : ℝ≥0) (y : ℝ) :
    BoundedDriftItoCharacteristics canonicalBrownianMeasure
      (canonicalBrownianShiftFiltration a) (zeroDriftBrownian β a y)
      (fun _ _ => 0) (canonicalDiracShiftMartingale β a) β := by
  refine ⟨continuous_zeroDriftBrownian β a y,stronglyAdapted_zeroDriftBrownian β a y,
    measurable_const,⟨0,by simp⟩,?_,martingale_canonicalDiracShiftMartingale β a,
    memLp_canonicalDiracShiftMartingale β a,?_⟩
  · intro t ω
    simp [zeroDriftBrownian,canonicalDiracShiftMartingale,integratedDrift]
  · intro T r
    convert quadraticVariation_canonicalDiracShiftMartingale β a T r using 1
    ext ω
    simp [integral_const,Measure.real,nonnegativeLebesgueMeasure_Ioc,smul_eq_mul,
      ENNReal.toReal_min,mul_comm]

end FRSB
