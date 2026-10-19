module
public import OverlapPaper.ReplicaSourceDefinitions
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-! The exact unit-curvature source bound for a genuine probability law.
This is applied to the actual marked terminal spin product, whose absolute
value is one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
namespace OverlapPaper

theorem source_log_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : AEMeasurable Y μ) (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ 1) (θ : ℝ) :
    Real.log (∫ ω, Real.exp (θ * Y ω) ∂μ) ≤
      θ * (∫ ω, Y ω ∂μ) + θ ^ 2 / 2 := by
  have hIcc : ∀ᵐ ω ∂μ, Y ω ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hSG := hasSubgaussianMGF_of_mem_Icc hY hIcc
  have HG := hSG.cgf_le θ
  have hparam : (‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) ^ 2 = (1 : NNReal) := by norm_num
  rw [hparam] at HG
  simp only [NNReal.coe_one, one_mul] at HG
  have hi : Integrable (fun ω => Real.exp (θ * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc hY hIcc
  have hpos := mgf_pos hi
  have hshift : cgf (fun ω => Y ω - ∫ ω, Y ω ∂μ) μ θ =
      Real.log (mgf Y μ θ) - θ * (∫ ω, Y ω ∂μ) := by
    simp only [cgf, sub_eq_add_neg]
    rw [mgf_add_const, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hshift] at HG
  change Real.log (mgf Y μ θ) ≤ _
  linarith only [HG]

end OverlapPaper
