module
public import FourPapersCommon.L2Moments

@[expose] public section

/-! The genuine L² norm and integral Cauchy--Schwarz bound for arbitrary
finite measures, used for coupled state integral equations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem norm_sq_toLp (f : Ω → ℝ) (hf : MemLp f 2 P) :
    ‖hf.toLp f‖^2 = ∫ ω,f ω^2 ∂P := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp [hω,RCLike.inner_apply,pow_two]

theorem norm_sq_sub_toLp (f g : Ω → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ‖hf.toLp f-hg.toLp g‖^2 = ∫ ω,(f ω-g ω)^2 ∂P := by
  rw [← hf.toLp_sub hg]
  exact norm_sq_toLp (f-g) (hf.sub hg)

theorem integral_sq_le_mass_mul_integral_sq [IsFiniteMeasure P]
    (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫ ω,f ω ∂P)^2 ≤ P.real Set.univ*(∫ ω,f ω^2 ∂P) := by
  let hi : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  let F := hf.toLp f
  let O := hi.toLp (fun _ : Ω => (1 : ℝ))
  have hinner : ⟪F,O⟫ = ∫ ω,f ω ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hi.coeFn_toLp] with ω hfω hiω
    change O ω * F ω = f ω
    rw [show F ω = f ω from hfω,show O ω = 1 from hiω,one_mul]
  have hh := real_inner_mul_inner_self_le F O
  rw [hinner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hh
  change (∫ ω,f ω ∂P)*(∫ ω,f ω ∂P) ≤ ‖hf.toLp f‖^2*‖hi.toLp (fun _ : Ω => (1 : ℝ))‖^2 at hh
  rw [norm_sq_toLp,norm_sq_toLp] at hh
  simpa only [one_pow,integral_const,smul_eq_mul,mul_one,one_mul,pow_two,mul_comm] using hh

end FourPapersCommon
