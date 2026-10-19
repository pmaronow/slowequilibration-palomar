module
public import QuantitativePaper.VectorMassRegularity
public import QuantitativePaper.VectorSpatialStep
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Gaussian covariance estimates give depth-independent positive-mass
variation bounds for actual vector Cole--Hopf steps. Convexity below concerns
the ordinary CGF; it is not Chen's stronger normalized-CGF theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ContDiff Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem hasDerivAt_vectorColeHopfStep_mass {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (v : ℝ) (x : Field n) {m : ℝ} (hm : m ≠ 0) :
    HasDerivAt (fun a => vectorColeHopfStep v a f x)
      ((deriv (cgf (fun z => f (fieldShift v x z)) (fieldGaussian n)) m*m-
        cgf (fun z => f (fieldShift v x z)) (fieldGaussian n) m)/m^2) m := by
  have hmem : m∈interior (integrableExpSet (fun z => f (fieldShift v x z)) (fieldGaussian n)) := by
    rw [vectorStep_integrableExpSet f K hf v x,interior_univ]
    trivial
  have hd := (analyticAt_cgf hmem).differentiableAt.hasDerivAt.div (hasDerivAt_id m) hm
  simp only [mul_one] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hm] with a ha
  simp [cgf,mgf,vectorColeHopfStep,vectorStepPartition,ha]

theorem convexOn_vectorStep_cgf {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (v : ℝ) (x : Field n) :
    ConvexOn ℝ univ (cgf (fun z => f (fieldShift v x z)) (fieldGaussian n)) := by
  have hmem (m : ℝ) : m∈interior (integrableExpSet (fun z => f (fieldShift v x z)) (fieldGaussian n)) := by
    rw [vectorStep_integrableExpSet f K hf v x,interior_univ]
    trivial
  apply convexOn_univ_of_deriv2_nonneg
    (fun m => (analyticAt_cgf (hmem m)).differentiableAt)
    (fun m => (analyticAt_cgf (hmem m)).deriv.differentiableAt)
  intro m
  have hh := iteratedDeriv_two_cgf_eq_integral (hmem m)
  have hpos := mgf_pos (integrable_exp_vectorStep f K hf v m x)
  have hn : 0 ≤ iteratedDeriv 2 (cgf (fun z => f (fieldShift v x z)) (fieldGaussian n)) m := by
    rw [hh]
    exact div_nonneg (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hpos.le
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.iterate_succ_apply',Function.iterate_zero_apply] using hn

theorem vectorColeHopfStep_mass_deriv_nonneg_pos {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (v : ℝ) (x : Field n) {m : ℝ} (hm : 0 < m) :
    0 ≤ deriv (fun a => vectorColeHopfStep v a f x) m := by
  have hmem : m∈interior (integrableExpSet (fun z => f (fieldShift v x z)) (fieldGaussian n)) := by
    rw [vectorStep_integrableExpSet f K hf v x,interior_univ]
    trivial
  have hs := (convexOn_vectorStep_cgf f K hf v x).slope_le_deriv (mem_univ 0) (mem_univ m)
    hm (analyticAt_cgf hmem).differentiableAt
  have hz : cgf (fun z => f (fieldShift v x z)) (fieldGaussian n) 0=0 := by simp
  simp only [slope,vsub_eq_sub,hz,sub_zero,smul_eq_mul] at hs
  rw [(hasDerivAt_vectorColeHopfStep_mass f K hf v x hm.ne').deriv]
  apply div_nonneg _ (sq_nonneg m)
  have ht := mul_le_mul_of_nonneg_right hs hm.le
  have he : (m⁻¹*cgf (fun z => f (fieldShift v x z)) (fieldGaussian n) m)*m=
      cgf (fun z => f (fieldShift v x z)) (fieldGaussian n) m := by field_simp
  rw [he] at ht
  linarith

theorem fieldShift_noise_dist {n : ℕ} (v : ℝ) (x y z : Field n) :
    dist (fieldShift v x y) (fieldShift v x z)=Real.sqrt v*dist y z := by
  simp [fieldShift,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem gaussian_cgf_deriv_sub_mean_bound {n : ℕ} (F : Field n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hF : ContDiff ℝ 1 F) (hLip : LipschitzWith L.toNNReal F)
    (m : ℝ) (hExp : ∀a,Integrable (fun z => Real.exp (a*F z)) (fieldGaussian n)) :
    |deriv (cgf F (fieldGaussian n)) m-∫z,F z ∂fieldGaussian n| ≤ L^2*|m| := by
  have hmem : m∈interior (integrableExpSet F (fieldGaussian n)) := by
    have he : integrableExpSet F (fieldGaussian n)=univ := Set.eq_univ_iff_forall.mpr hExp
    rw [he,interior_univ]
    trivial
  have hgrad (z : Field n) : ‖gradient F z‖ ≤ L := by
    rw [gradient,LinearIsometryEquiv.norm_map]
    have hh := norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := z)
    simpa only [Real.coe_toNNReal _ hL] using hh
  have hc := SYK.gaussian_cov_bound_smooth F L hL hF hgrad m
  rw [deriv_cgf hmem,div_sub',abs_div,abs_of_pos (mgf_pos (hExp m))]
  · apply (div_le_iff₀ (mgf_pos (hExp m))).mpr
    simpa only [mgf,mul_comm] using hc
  · exact (mgf_pos (hExp m)).ne'

theorem vectorColeHopfStep_mass_deriv_le_pos {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hSmooth : ContDiff ℝ 1 f) (v : ℝ) (x : Field n)
    {m : ℝ} (hm : 0 < m) :
    deriv (fun a => vectorColeHopfStep v a f x) m ≤ ((K : ℝ)*Real.sqrt v)^2 := by
  let F := fun z : Field n => f (fieldShift v x z)
  let L := (K : ℝ)*Real.sqrt v
  have hL : 0 ≤ L := mul_nonneg K.coe_nonneg (Real.sqrt_nonneg v)
  have hF : ContDiff ℝ 1 F := hSmooth.comp (by unfold fieldShift;fun_prop)
  have hLip : LipschitzWith L.toNNReal F := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.coe_toNNReal _ hL]
    have hh := hf.dist_le_mul (fieldShift v x y) (fieldShift v x z)
    rw [fieldShift_noise_dist] at hh
    simpa only [F,L,mul_assoc] using hh
  have hExp (a : ℝ) : Integrable (fun z => Real.exp (a*F z)) (fieldGaussian n) :=
    integrable_exp_vectorStep f K hf v a x
  have hb := (abs_le.mp (gaussian_cgf_deriv_sub_mean_bound F L hL hF hLip m hExp)).2
  rw [abs_of_pos hm] at hb
  have hmem : (0 : ℝ)∈interior (integrableExpSet F (fieldGaussian n)) := by
    rw [vectorStep_integrableExpSet f K hf v x,interior_univ]
    trivial
  have hs := (convexOn_vectorStep_cgf f K hf v x).deriv_le_slope (mem_univ 0) (mem_univ m)
    hm (analyticAt_cgf hmem).differentiableAt
  have hz : cgf F (fieldGaussian n) 0=0 := by simp
  change deriv (cgf F (fieldGaussian n)) 0 ≤ slope (cgf F (fieldGaussian n)) 0 m at hs
  rw [deriv_cgf_zero hmem] at hs
  simp only [probReal_univ,div_one,slope,vsub_eq_sub,hz,sub_zero,smul_eq_mul] at hs
  have hlower : m*(∫z,F z ∂fieldGaussian n) ≤ cgf F (fieldGaussian n) m := by
    have hh := mul_le_mul_of_nonneg_right hs hm.le
    have he : (m⁻¹*cgf F (fieldGaussian n) m)*m=cgf F (fieldGaussian n) m := by field_simp
    rw [he] at hh
    nlinarith
  rw [(hasDerivAt_vectorColeHopfStep_mass f K hf v x hm.ne').deriv]
  apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
  have hmul := mul_le_mul_of_nonneg_left hb hm.le
  change deriv (cgf F (fieldGaussian n)) m*m-cgf F (fieldGaussian n) m ≤ L^2*m^2
  nlinarith

theorem vectorColeHopfStep_mass_deriv_bounds_nonneg {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hSmooth : ContDiff ℝ 1 f) (v : ℝ) (x : Field n)
    {m : ℝ} (hm : 0 ≤ m) :
    0 ≤ deriv (fun a => vectorColeHopfStep v a f x) m ∧
    deriv (fun a => vectorColeHopfStep v a f x) m ≤ ((K : ℝ)*Real.sqrt v)^2 := by
  rcases eq_or_lt_of_le hm with hm|hm
  · subst m
    refine ⟨?_,?_⟩
    · rw [(hasDerivAt_vectorColeHopfStep_mass_zero f K hf v x).deriv]
      exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
    · have hc := (analyticAt_vectorColeHopfStep_mass f K hf v x 0).deriv.continuousAt
      have hd : Tendsto (deriv (fun a => vectorColeHopfStep v a f x)) (𝓝[>] (0 : ℝ))
          (𝓝 (deriv (fun a => vectorColeHopfStep v a f x) 0)) :=
        hc.tendsto.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto hd (by
        filter_upwards [self_mem_nhdsWithin] with a ha
        exact vectorColeHopfStep_mass_deriv_le_pos f K hf hSmooth v x ha)
  · exact ⟨vectorColeHopfStep_mass_deriv_nonneg_pos f K hf v x hm,
      vectorColeHopfStep_mass_deriv_le_pos f K hf hSmooth v x hm⟩

theorem vectorColeHopfStep_mass_abs_sub_le {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hSmooth : ContDiff ℝ 1 f) (v : ℝ) (x : Field n)
    (m a : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) :
    |vectorColeHopfStep v a f x-vectorColeHopfStep v m f x| ≤
      ((K : ℝ)*Real.sqrt v)^2*|a-m| := by
  have hd := differentiable_vectorColeHopfStep_mass f K hf v x
  have hh := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun u (_hu : u∈Ici (0 : ℝ)) => hd u)
    (fun u (hu : u∈Ici (0 : ℝ)) => by
      have hb := vectorColeHopfStep_mass_deriv_bounds_nonneg f K hf hSmooth v x hu
      rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
      exact hb.2) hm ha
  simpa only [Real.norm_eq_abs] using hh

theorem vectorColeHopfStep_recursion_mass_abs_sub_le {n k : ℕ} (s : RSBScheme k)
    (β t v : ℝ) (hv : 0 ≤ v) (p : Couplings n × ℝ) (j : ℕ) (x : Field n)
    (m a : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) :
    |vectorColeHopfStep v a (vectorRecursion s β t p j) x-
      vectorColeHopfStep v m (vectorRecursion s β t p j) x| ≤ (n : ℝ)*v*|a-m| := by
  have hh := vectorColeHopfStep_mass_abs_sub_le (vectorRecursion s β t p j) _
    (vectorRecursion_lipschitz s β t p j) ((contDiff_vectorRecursion_field s β t p j).of_le (by simp))
    v x m a hm ha
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt hv] at hh
  exact hh

end QuantitativePaper
