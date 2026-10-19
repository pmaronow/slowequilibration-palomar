module
public import QuantitativePaper.VectorMassBounds
public import QuantitativePaper.VectorMagnetizationSmooth
public import QuantitativePaper.VectorConvexity
public import QuantitativeFollowup.ChenStandardGaussian

@[expose] public section

/-! The sharp half-variance coefficient bound for the actual convex
Cole--Hopf recursion. Chen convexity and the proved Gaussian quadratic CGF
bound control the derivative of the genuine removable mass quotient. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

/-- A convex differentiable function with an affine upper bound on the
positive half-line has derivative at most that upper bound's slope. -/
theorem convex_deriv_le_of_positive_affine_bound (f : ℝ→ℝ)
    (hc : ConvexOn ℝ univ f) (hd : Differentiable ℝ f) (a b : ℝ)
    (hb : ∀y,0<y→f y≤a+b*y) (x : ℝ) : deriv f x≤b := by
  have hden : Tendsto (fun y:ℝ=>y-x) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using (tendsto_atTop_add_const_right atTop (-x) tendsto_id)
  have ht : Tendsto (fun y:ℝ=>b+(a+b*x-f x)/(y-x)) atTop (𝓝 b) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x:=b)).add ((tendsto_const_nhds (x:=a+b*x-f x)).div_atTop hden)
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop (max x 0)] with y hy
  have hxy : x<y := lt_of_le_of_lt (le_max_left _ _) hy
  have hy0 : 0<y := lt_of_le_of_lt (le_max_right _ _) hy
  have hs := hc.deriv_le_slope (mem_univ x) (mem_univ y) hxy (hd x)
  have hbound := hb y hy0
  have hden : 0<y-x := sub_pos.mpr hxy
  change deriv f x≤(y-x)⁻¹*(f y-f x) at hs
  calc
    _ ≤ (f y-f x)/(y-x) := by simpa only [div_eq_mul_inv,mul_comm] using hs
    _ ≤ (a+b*y-f x)/(y-x) := div_le_div_of_nonneg_right (sub_le_sub_right hbound _) hden.le
    _ = b+(a+b*x-f x)/(y-x) := by field_simp;ring

theorem fieldGaussian_eq_stdGaussian (n : ℕ) : fieldGaussian n=stdGaussian (Field n) :=
  map_pi_eq_stdGaussian

/-- Actual smooth convex Gaussian data have a sharp derivative bound for
their normalized log moment, including the removable value at zero. -/
theorem gaussian_normalizedCGF_deriv_le_half {n : ℕ} (F : Field n→ℝ)
    (hJets : BoundedPositiveJets F) (hconv : ConvexOn ℝ univ F)
    (L : ℝ) (hL : 0≤L) (hLip : LipschitzWith L.toNNReal F)
    (hExp : ∀a,Integrable (fun z=>Real.exp (a*F z)) (fieldGaussian n)) (m : ℝ) :
    deriv (normalizedCGF (fieldGaussian n) F) m≤L^2/2 := by
  have hmem (a : ℝ) : a∈interior (integrableExpSet F (fieldGaussian n)) := by
    have he : integrableExpSet F (fieldGaussian n)=univ := Set.eq_univ_iff_forall.mpr hExp
    rw [he,interior_univ]
    trivial
  have hcgf : Differentiable ℝ (cgf F (fieldGaussian n)) :=
    fun a=>(analyticAt_cgf (hmem a)).differentiableAt
  have hquad (a : ℝ) : cgf F (fieldGaussian n) a≤
      (∫z,F z ∂fieldGaussian n)*a+L^2*a^2/2 :=
    SYK.quadratic_bound_of_deriv_sub_le hcgf (by simp)
      (fun a=>gaussian_cgf_deriv_sub_mean_bound F L hL
        (hJets.1.of_le (by simp)) hLip a hExp) a
  have hc : ConvexOn ℝ univ (normalizedCGF (fieldGaussian n) F) := by
    rw [fieldGaussian_eq_stdGaussian]
    exact convexOn_normalizedCGF_stdGaussian hJets hconv
  have hd : Differentiable ℝ (normalizedCGF (fieldGaussian n) F) := by
    intro a
    by_cases ha : a=0
    · subst a
      exact (analyticAt_normalizedCGF_zero _ _ (hmem 0)).differentiableAt
    · have he : normalizedCGF (fieldGaussian n) F =ᶠ[𝓝 a]
          fun b=>cgf F (fieldGaussian n) b/b := by
        filter_upwards [eventually_ne_nhds ha] with b hb
        exact normalizedCGF_of_ne _ _ hb
      exact ((hcgf a).div differentiableAt_id ha).congr_of_eventuallyEq he
  apply convex_deriv_le_of_positive_affine_bound _ hc hd (∫z,F z ∂fieldGaussian n) (L^2/2)
  intro a ha
  rw [normalizedCGF_of_ne _ _ ha.ne']
  apply (div_le_iff₀ ha).mpr
  convert! hquad a using 1 <;> ring

/-- The actual convex finite recursion is valid Chen data after the true
Gaussian shift, with its global positive-order derivative bounds proved. -/
theorem boundedPositiveJets_vectorRecursion_noise {n k : ℕ} (s : RSBScheme k)
    (β t v : ℝ) (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    BoundedPositiveJets (fun z=>vectorRecursion s β t p j (fieldShift v x z)) := by
  have hh := (boundedPositiveJets_translate (boundedPositiveJets_vectorRecursion_joint s β t j)
    (p,x)).comp_linear (vectorJointShift n v)
  simpa only [Function.comp_def,vectorJointShift_add] using hh

theorem convexOn_vectorRecursion_noise {n k : ℕ} (s : RSBScheme k)
    (β t v : ℝ) (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    ConvexOn ℝ univ (fun z=>vectorRecursion s β t p j (fieldShift v x z)) := by
  have hh := ((convexOn_vectorRecursion_joint s β t j).translate_right (p,x)).comp_linearMap
    (vectorJointShift n v).toLinearMap
  simp only [preimage_univ,Function.comp_def] at hh
  have he : (fun z:Field n=>vectorRecursion s β t ((p,x)+vectorJointShift n v z).1 j
      ((p,x)+vectorJointShift n v z).2)=
      (fun z=>vectorRecursion s β t p j (fieldShift v x z)) := by
    funext z
    rw [vectorJointShift_add]
  change ConvexOn ℝ univ (fun z:Field n=>vectorRecursion s β t ((p,x)+vectorJointShift n v z).1 j
    ((p,x)+vectorJointShift n v z).2) at hh
  rw [he] at hh
  exact hh

theorem vectorColeHopfStep_recursion_mass_deriv_le_half {n k : ℕ} (s : RSBScheme k)
    (β t v : ℝ) (hv : 0≤v) (p : Couplings n×ℝ) (j : ℕ) (x : Field n) (m : ℝ) :
    deriv (fun a=>vectorColeHopfStep v a (vectorRecursion s β t p j) x) m≤(n:ℝ)*v/2 := by
  let F := fun z=>vectorRecursion s β t p j (fieldShift v x z)
  let L := Real.sqrt (n:ℝ)*Real.sqrt v
  have hL : 0≤L := by positivity
  have hLip : LipschitzWith L.toNNReal F := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.coe_toNNReal _ hL]
    have hh := (vectorRecursion_lipschitz s β t p j).dist_le_mul
      (fieldShift v x y) (fieldShift v x z)
    rw [fieldShift_noise_dist,Real.coe_toNNReal _ (Real.sqrt_nonneg _)] at hh
    simpa only [F,L,mul_assoc] using hh
  have hh := gaussian_normalizedCGF_deriv_le_half F
    (boundedPositiveJets_vectorRecursion_noise s β t v p j x)
    (convexOn_vectorRecursion_noise s β t v p j x) L hL hLip
    (fun a=>integrable_exp_vectorStep _ _ (vectorRecursion_lipschitz s β t p j) v a x) m
  rw [vectorColeHopfStep_eq_dslope_cgf _ _ (vectorRecursion_lipschitz s β t p j) v x]
  change deriv (normalizedCGF (fieldGaussian n) F) m≤_
  rw [show L^2=(n:ℝ)*v by
    dsimp only [L];rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt hv]] at hh
  exact hh

theorem vectorColeHopfStep_recursion_mass_abs_sub_le_half {n k : ℕ} (s : RSBScheme k)
    (β t v : ℝ) (hv : 0≤v) (p : Couplings n×ℝ) (j : ℕ) (x : Field n)
    (m a : ℝ) (hm : 0 ≤ m) (ha : 0 ≤ a) :
    |vectorColeHopfStep v a (vectorRecursion s β t p j) x-
      vectorColeHopfStep v m (vectorRecursion s β t p j) x|≤(n:ℝ)*v/2*|a-m| := by
  have hd := differentiable_vectorColeHopfStep_mass _ _ (vectorRecursion_lipschitz s β t p j) v x
  have hh := (convex_Ici (0:ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun u _=>hd u) (fun u hu=>by
      have hn := (vectorColeHopfStep_mass_deriv_bounds_nonneg _ _
        (vectorRecursion_lipschitz s β t p j)
        ((contDiff_vectorRecursion_field s β t p j).of_le (by simp)) v x hu).1
      rw [Real.norm_eq_abs,abs_of_nonneg hn]
      exact vectorColeHopfStep_recursion_mass_deriv_le_half s β t v hv p j x u) hm ha
  simpa only [Real.norm_eq_abs] using hh

end QuantitativePaper
