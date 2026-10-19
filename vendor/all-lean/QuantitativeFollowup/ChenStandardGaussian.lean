module
public import QuantitativeFollowup.ChenGaussianSum
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-! The independent sum over an orthonormal basis is the actual standard
Gaussian law. This identifies the control-derived convexity with Gaussian CGFs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal RealInnerProductSpace
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
set_option maxHeartbeats 1000000

theorem charFun_gaussianDirectionSumLaw (vs : List E) (t : E) :
    charFun (gaussianDirectionSumLaw vs) t=
      Complex.exp (-((vs.map (fun v=>⟪v,t⟫^2)).sum : ℝ)/2) := by
  induction vs with
  | nil => simp [gaussianDirectionSumLaw,charFun_apply]
  | cons v vs ih =>
    rw [charFun_apply,gaussianDirectionSumLaw,integral_map
      (by fun_prop : Measurable (fun p : ℝ × E=>p.1 • v+p.2)).aemeasurable
      (by fun_prop)]
    have he (p : ℝ × E) :
        Complex.exp ((⟪p.1 • v+p.2,t⟫ : ℝ)*Complex.I)=
          Complex.exp ((⟪p.1 • v,t⟫ : ℝ)*Complex.I)*Complex.exp ((⟪p.2,t⟫ : ℝ)*Complex.I) := by
      rw [inner_add_left,Complex.ofReal_add,add_mul,Complex.exp_add]
    simp_rw [he]
    have hprod : (∫ p : ℝ × E,Complex.exp ((⟪p.1 • v,t⟫ : ℝ)*Complex.I)*
        Complex.exp ((⟪p.2,t⟫ : ℝ)*Complex.I)
        ∂(gaussianReal 0 1).prod (gaussianDirectionSumLaw vs))=
      (∫ z : ℝ,Complex.exp ((⟪z • v,t⟫ : ℝ)*Complex.I) ∂gaussianReal 0 1)*
      (∫ y : E,Complex.exp ((⟪y,t⟫ : ℝ)*Complex.I) ∂gaussianDirectionSumLaw vs) := by
      convert! integral_prod_mul
        (μ:=gaussianReal 0 1) (ν:=gaussianDirectionSumLaw vs)
        (fun z : ℝ=>Complex.exp ((⟪z • v,t⟫ : ℝ)*Complex.I))
        (fun y : E=>Complex.exp ((⟪y,t⟫ : ℝ)*Complex.I)) using 1
    rw [hprod]
    have hg : (∫ z : ℝ,Complex.exp ((⟪z • v,t⟫ : ℝ)*Complex.I) ∂gaussianReal 0 1)=
        Complex.exp (-((⟪v,t⟫^2 : ℝ) : ℂ)/2) := by
      simp only [real_inner_smul_left,Complex.ofReal_mul,mul_comm _ (⟪v,t⟫),←charFun_apply_real,
        charFun_gaussianReal,Complex.ofReal_zero,mul_zero,zero_mul,NNReal.coe_one,
        Complex.ofReal_one,one_mul,zero_sub,Complex.ofReal_pow]
      congr 1
      ring
    rw [hg,←charFun_apply,ih,←Complex.exp_add]
    congr 1
    simp only [List.map_cons,List.sum_cons,Complex.ofReal_add]
    ring

theorem gaussianDirectionSumLaw_orthonormalBasis [CompleteSpace E] [FiniteDimensional ℝ E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) :
    gaussianDirectionSumLaw (List.ofFn b)=stdGaussian E := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_gaussianDirectionSumLaw,charFun_stdGaussian]
  have he : ((List.ofFn b).map (fun v=>⟪v,t⟫^2)).sum=‖t‖^2 := by
    rw [List.map_ofFn,List.sum_ofFn]
    exact b.sum_sq_inner_right t
  rw [he]
  simp only [Complex.ofReal_pow]

theorem convexOn_normalizedCGF_stdGaussian [CompleteSpace E] [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : BoundedPositiveJets f) (hconv : ConvexOn ℝ univ f) :
    ConvexOn ℝ univ (normalizedCGF (stdGaussian E) f) := by
  have hh := convexOn_normalizedCGF_gaussianDirectionSum hf hconv
    (List.ofFn (stdOrthonormalBasis ℝ E)) 0
  rw [gaussianDirectionSumLaw_orthonormalBasis] at hh
  simpa only [zero_add] using hh

end QuantitativeFollowup
