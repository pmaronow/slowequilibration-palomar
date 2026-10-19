module
public import QuantitativePaper.SmoothGaussianAverage
public import QuantitativePaper.FiniteJetBounds

@[expose] public section

/-! Higher regularity and uniform positive-order jet bounds for the actual
Gaussian Cole--Hopf operation, including its zero-mass branch. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussianShiftColeHopf {n : ℕ} (A : Field n →L[ℝ] E) (m : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  if m = 0 then gaussianShiftAverage A f x else Real.log (gaussianShiftPartition A m f x)/m

theorem gaussianShiftColeHopf_smooth_bounded_jets {n : ℕ} (N : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 1 ≤ K)
    (hjets : ∀ j,1 ≤ j → j ≤ N → ∀ x,‖iteratedFDeriv ℝ j f x‖ ≤ K^j)
    (A : Field n →L[ℝ] E) (m : ℝ) :
    ContDiff ℝ N (gaussianShiftColeHopf A m f) ∧
    ∃ D : ℝ,1 ≤ D ∧ ∀ j,1 ≤ j → j ≤ N → ∀ x,
      ‖iteratedFDeriv ℝ j (gaussianShiftColeHopf A m f) x‖ ≤ D^j := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  by_cases hm : m = 0
  · have he : gaussianShiftColeHopf A m f = gaussianShiftAverage A f :=
      funext fun x => by simp [gaussianShiftColeHopf,hm]
    rw [he]
    exact ⟨contDiff_gaussianShiftAverage N f hf L hlip K hK0 hjets A,
      K,hK,fun j hj0 hj x => norm_iteratedFDeriv_gaussianShiftAverage_le N j f hf L hlip K hK0 hjets A hj0 hj x⟩
  · have hZ := contDiff_gaussianShiftPartition N f hf L hlip K hK0 hjets A m
    have hlog : ContDiff ℝ N (fun y => Real.log (gaussianShiftPartition A m f y)) :=
      hZ.log (fun y => (gaussianShiftPartition_pos f L hlip A m y).ne')
    have hfun : gaussianShiftColeHopf A m f = fun y => m⁻¹*Real.log (gaussianShiftPartition A m f y) :=
      funext fun y => by simp [gaussianShiftColeHopf,hm,div_eq_mul_inv,mul_comm]
    have hStep : ContDiff ℝ N (gaussianShiftColeHopf A m f) := by
      rw [hfun]
      exact contDiff_const.mul hlog
    let B := fun j => |m⁻¹| * ((j.factorial : ℝ)*logJetCoefficient j*(gaussianDerivativePowerBound m K N)^j)
    refine ⟨hStep,finiteJetPowerBound B N,finiteJetPowerBound_ge_one B N,?_⟩
    intro j hj0 hj x
    have hlogj := hlog.of_le (show (j : ℕ∞ω) ≤ N by norm_cast)
    have he : iteratedFDeriv ℝ j (gaussianShiftColeHopf A m f) x =
        m⁻¹ • iteratedFDeriv ℝ j (fun y => Real.log (gaussianShiftPartition A m f y)) x := by
      rw [hfun]
      exact iteratedFDeriv_const_smul_apply' (a := m⁻¹) (x := x) hlogj.contDiffAt
    rw [he,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_log_gaussianShiftPartition_le N j f hf L hlip K hK0 hjets A m hj0 hj x)
      (abs_nonneg _)).trans (finite_jet_bound_le_power B N j hj0 hj)

end QuantitativePaper
