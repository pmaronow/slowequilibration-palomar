module
public import QuantitativeFollowup.ChenCoordinateIteration
public import FourPapersCommon.NormalizedCGFGlobal

@[expose] public section

/-! Actual independent Gaussian sums underlying coordinate smoothing. Genuine
exponential integrability supplies Fubini; no factorization premise is required. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper ColeHopfFoundation.ProbabilityTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
set_option maxHeartbeats 1000000

def gaussianDirectionSumLaw : List E → Measure E
  | []=>Measure.dirac 0
  | v::vs=>((gaussianReal 0 1).prod (gaussianDirectionSumLaw vs)).map (fun p=>p.1 • v+p.2)

instance isProbabilityMeasure_gaussianDirectionSumLaw (vs : List E) :
    IsProbabilityMeasure (gaussianDirectionSumLaw vs) := by
  induction vs with
  | nil => change IsProbabilityMeasure (Measure.dirac (0:E));infer_instance
  | cons v vs ih =>
    letI := ih
    change IsProbabilityMeasure (((gaussianReal 0 1).prod (gaussianDirectionSumLaw vs)).map
      (fun p : ℝ × E=>p.1 • v+p.2))
    infer_instance

theorem integrable_exp_norm_gaussianDirectionSumLaw (vs : List E) (C : ℝ) (hC : 0 ≤ C) :
    Integrable (fun y=>Real.exp (C*‖y‖)) (gaussianDirectionSumLaw vs) := by
  induction vs with
  | nil => exact integrable_dirac (by simp)
  | cons v vs ih =>
    have hm : Measurable (fun p : ℝ × E=>p.1 • v+p.2) := by fun_prop
    change Integrable _ (((gaussianReal 0 1).prod (gaussianDirectionSumLaw vs)).map _)
    apply (integrable_map_measure (by fun_prop : AEStronglyMeasurable
      (fun y : E=>Real.exp (C*‖y‖)) _ ) hm.aemeasurable).mpr
    have hleft := SpinGlass.integrable_exp_abs_mul_stdGaussian (C*‖v‖)
    apply (hleft.mul_prod ih).mono' (by fun_prop)
    apply Eventually.of_forall
    rintro ⟨z,y⟩
    change ‖Real.exp (C*‖z • v+y‖)‖ ≤ Real.exp ((C*‖v‖)*|z|)*Real.exp (C*‖y‖)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    change Real.exp (C*‖z • v+y‖) ≤ Real.exp ((C*‖v‖)*|z|)*Real.exp (C*‖y‖)
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (norm_add_le (z • v) y) hC
    rw [norm_smul,Real.norm_eq_abs] at hh
    nlinarith

theorem integrable_exp_gaussianDirectionSumLaw {f : E → ℝ} (L : ℝ≥0)
    (hf : LipschitzWith L f) (vs : List E) (m : ℝ) (x : E) :
    Integrable (fun y=>Real.exp (m*f (x+y))) (gaussianDirectionSumLaw vs) := by
  have hc : Continuous f := hf.continuous
  have hi := (integrable_exp_norm_gaussianDirectionSumLaw vs (|m| *(L:ℝ)) (by positivity)).const_mul
    (Real.exp (|m| *|f x|))
  apply hi.mono' (by fun_prop)
  apply Eventually.of_forall
  intro y
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd := hf.dist_le_mul (x+y) x
  simp only [dist_eq_norm,add_sub_cancel_left,Real.norm_eq_abs] at hd
  have hbound : |f (x+y)| ≤ |f x|+(L:ℝ)*‖y‖ := by
    calc
      _ ≤ |f x|+|f (x+y)-f x| := by
        convert abs_add_le (f x) (f (x+y)-f x) using 1 <;> congr 1 <;> ring
      _ ≤ _ := add_le_add_right hd _
  calc
    m*f (x+y) ≤ |m| *|f (x+y)| := le_abs_self _ |>.trans_eq (abs_mul _ _)
    _ ≤ |m| *(|f x|+(L:ℝ)*‖y‖) := mul_le_mul_of_nonneg_left hbound (abs_nonneg m)
    _ = _ := by ring

def gaussianDirectionPartition (vs : List E) (f : E → ℝ) (m : ℝ) (x : E) : ℝ :=
  ∫ y,Real.exp (m*f (x+y)) ∂gaussianDirectionSumLaw vs

theorem gaussianDirectionPartition_pos {f : E → ℝ} (L : ℝ≥0) (hf : LipschitzWith L f)
    (vs : List E) (m : ℝ) (x : E) : 0 < gaussianDirectionPartition vs f m x := by
  apply (integral_pos_iff_support_of_nonneg (fun _=>(Real.exp_pos _).le)
    (integrable_exp_gaussianDirectionSumLaw L hf vs m x)).mpr
  have he : Function.support (fun y=>Real.exp (m*f (x+y)))=univ := by
    ext y;simp [Function.mem_support,Real.exp_ne_zero]
  rw [he,measure_univ]
  norm_num

theorem gaussianDirectionPartition_cons {f : E → ℝ} (L : ℝ≥0) (hf : LipschitzWith L f)
    (v : E) (vs : List E) (m : ℝ) (x : E) :
    gaussianDirectionPartition (v::vs) f m x=
      ∫ z,gaussianDirectionPartition vs f m (x+z • v) ∂gaussianReal 0 1 := by
  have hc : Continuous f := hf.continuous
  have hm : Measurable (fun p : ℝ × E=>p.1 • v+p.2) := by fun_prop
  have hi := (integrable_map_measure
    (by fun_prop : AEStronglyMeasurable (fun y=>Real.exp (m*f (x+y)))
      (((gaussianReal 0 1).prod (gaussianDirectionSumLaw vs)).map _)) hm.aemeasurable).mp
    (integrable_exp_gaussianDirectionSumLaw L hf (v::vs) m x)
  change (∫ y,Real.exp (m*f (x+y))
    ∂(((gaussianReal 0 1).prod (gaussianDirectionSumLaw vs)).map (fun p : ℝ × E=>p.1 • v+p.2)))=
      ∫ z,(∫ y,Real.exp (m*f ((x+z • v)+y)) ∂gaussianDirectionSumLaw vs) ∂gaussianReal 0 1
  rw [integral_map hm.aemeasurable (by fun_prop)]
  simpa only [Function.comp_apply,add_assoc] using integral_prod _ hi


theorem iteratedScalarGaussian_eq_log_partition {f : E → ℝ} (hf : BoundedPositiveJets f)
    (vs : List E) (m : ℝ) (hm : m ≠ 0) (x : E) :
    iteratedScalarGaussian vs (fun p=>f p.2) (m,x)=
      Real.log (gaussianDirectionPartition vs f m x)/m := by
  obtain ⟨L,hL⟩ := exists_lipschitz_of_boundedPositiveJets hf
  induction vs generalizing x with
  | nil =>
    simp only [iteratedScalarGaussian,gaussianDirectionPartition,gaussianDirectionSumLaw,integral_dirac,add_zero,Real.log_exp]
    exact (mul_div_cancel_left₀ (f x) hm).symm
  | cons v vs ih =>
    have he (z : ℝ) :
        Real.exp (m*iteratedScalarGaussian vs (fun p=>f p.2) (m,x+z • v))=
          gaussianDirectionPartition vs f m (x+z • v) := by
      rw [ih,mul_div_cancel₀ _ hm,Real.exp_log (gaussianDirectionPartition_pos L hL vs m (x+z • v))]
    simp only [iteratedScalarGaussian,gaussianCoordinateStep,coleHopf,if_neg hm,zero_add]
    simp_rw [he]
    rw [←gaussianDirectionPartition_cons L hL v vs m x]
    ring

theorem normalizedCGF_gaussianDirectionSum_eq_iteration {f : E → ℝ}
    (hf : BoundedPositiveJets f) (vs : List E) (x : E) (m : ℝ) (hm : m ≠ 0) :
    normalizedCGF (gaussianDirectionSumLaw vs) (fun y=>f (x+y)) m=
      iteratedScalarGaussian vs (fun p=>f p.2) (m,x) := by
  rw [normalizedCGF_of_ne _ _ hm,iteratedScalarGaussian_eq_log_partition hf vs m hm x]
  rfl

theorem integrableExpSet_gaussianDirectionSum_eq_univ {f : E → ℝ}
    (hf : BoundedPositiveJets f) (vs : List E) (x : E) :
    integrableExpSet (fun y=>f (x+y)) (gaussianDirectionSumLaw vs)=univ := by
  obtain ⟨L,hL⟩ := exists_lipschitz_of_boundedPositiveJets hf
  ext m
  exact ⟨fun _=>mem_univ _,fun _=>integrable_exp_gaussianDirectionSumLaw L hL vs m x⟩

theorem convexOn_terminalGaussianFamily {S : Set ℝ} (hS : Convex ℝ S)
    {f : E → ℝ} (hf : ConvexOn ℝ univ f) :
    ConvexOn ℝ (S ×ˢ (univ : Set E)) (fun p : ℝ × E=>f p.2) := by
  refine ⟨hS.prod convex_univ,?_⟩
  rintro ⟨m0,x0⟩ _ ⟨m1,x1⟩ _ a b ha hb hab
  exact hf.2 (mem_univ x0) (mem_univ x1) ha hb hab

theorem convexOn_normalizedCGF_gaussianDirectionSum {f : E → ℝ}
    (hf : BoundedPositiveJets f) (hconv : ConvexOn ℝ univ f) (vs : List E) (x : E) :
    ConvexOn ℝ univ (normalizedCGF (gaussianDirectionSumLaw vs) (fun y=>f (x+y))) := by
  have hp := convexOn_iteratedScalarGaussian_positive vs (fun p=>f p.2)
    (convexOn_terminalGaussianFamily (convex_Ioi 0) hconv) (fun _=>hf)
  have hn := convexOn_iteratedScalarGaussian_negative vs (fun p=>f p.2)
    (convexOn_terminalGaussianFamily (convex_Iio 0) hconv) (fun _=>hf)
  have hslice {S : Set ℝ} (hS : Convex ℝ S)
      (hF : ConvexOn ℝ (S ×ˢ (univ : Set E)) (iteratedScalarGaussian vs (fun p=>f p.2))) :
      ConvexOn ℝ S (fun m=>iteratedScalarGaussian vs (fun p=>f p.2) (m,x)) := by
    refine ⟨hS,?_⟩
    intro m0 hm0 m1 hm1 a b ha hb hab
    have hh := hF.2 (show (m0,x)∈S ×ˢ (univ : Set E) from ⟨hm0,mem_univ _⟩)
      (show (m1,x)∈S ×ˢ (univ : Set E) from ⟨hm1,mem_univ _⟩) ha hb hab
    have he : a • x+b • x=x := by rw [←add_smul,hab,one_smul]
    change iteratedScalarGaussian vs (fun p=>f p.2) (a*m0+b*m1,a • x+b • x) ≤ _ at hh
    rw [he] at hh
    exact hh
  apply convexOn_normalizedCGF_of_signed_halfLines _ _ (integrableExpSet_gaussianDirectionSum_eq_univ hf vs x)
  · apply (hslice (convex_Iio 0) hn).congr
    intro m hm
    exact (normalizedCGF_gaussianDirectionSum_eq_iteration hf vs x m hm.ne).symm
  · apply (hslice (convex_Ioi 0) hp).congr
    intro m hm
    exact (normalizedCGF_gaussianDirectionSum_eq_iteration hf vs x m hm.ne').symm

end QuantitativeFollowup
