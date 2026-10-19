-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalForm
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Intrinsic C^m functions on the actual round sphere have genuine global
ambient C^m representatives. Intrinsic regularity is measured in the standard
analytic sphere atlas, transported by the canonical radius dilation. -/
@[expose] public section
namespace SlowEquilibration.SphericalIntrinsicExtension
open Set Filter Metric Function TopologicalSpace
open SphericalModel SphericalForm
open scoped Topology Manifold ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

abbrev RoundSphere (n : ℕ) := {x : Vector (n+1) // ‖x‖^2=(n+1 : ℕ)}
abbrev UnitSphere (n : ℕ) := ↥(sphere (0 : Vector (n+1)) 1)

def unitToRound (n : ℕ) (u : UnitSphere n) : RoundSphere n :=
  ⟨Real.sqrt (n+1 : ℕ) • (u : Vector (n+1)),by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      show ‖(u : Vector (n+1))‖=1 from mem_sphere_zero_iff_norm.mp u.property,
      one_pow,mul_one,Real.sq_sqrt (Nat.cast_nonneg _)]⟩

def roundToUnit (n : ℕ) (x : RoundSphere n) : UnitSphere n :=
  ⟨(Real.sqrt (n+1 : ℕ))⁻¹ • (x : Vector (n+1)),by
    have hs : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hn : ‖(x : Vector (n+1))‖=Real.sqrt (n+1 : ℕ) := by
      exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt x.property)
    simp only [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_inv,
      abs_of_pos hs,hn,inv_mul_cancel₀ hs.ne']⟩

/-- The literal sphere of radius sqrt(N) is homeomorphic to the standard
unit sphere by the actual ambient radius dilation. -/
def radiusDilation (n : ℕ) : UnitSphere n ≃ₜ RoundSphere n where
  toFun := unitToRound n
  invFun := roundToUnit n
  left_inv u := by
    apply Subtype.ext
    change (Real.sqrt (n+1 : ℕ))⁻¹ • (Real.sqrt (n+1 : ℕ) • (u : Vector (n+1))) = _
    rw [smul_smul,inv_mul_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne',one_smul]
  right_inv x := by
    apply Subtype.ext
    change Real.sqrt (n+1 : ℕ) • ((Real.sqrt (n+1 : ℕ))⁻¹ • (x : Vector (n+1))) = _
    rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne',one_smul]
  continuous_toFun := by
    unfold unitToRound
    fun_prop
  continuous_invFun := by
    unfold roundToUnit
    fun_prop

/-- Intrinsic C^m regularity on the actual round sphere, using its canonical
radius dilation and Mathlib's genuine analytic stereographic sphere atlas. -/
def IntrinsicContDiff (n : ℕ) (m : ℕ∞) (f : RoundSphere n → ℝ) : Prop :=
  ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) m (f ∘ unitToRound n)

def punctured (n : ℕ) : Opens (Vector (n+1)) := ⟨{x | x ≠ 0},isOpen_ne⟩

def radialUnit (n : ℕ) (x : punctured n) : UnitSphere n :=
  ⟨‖(x : Vector (n+1))‖⁻¹ • (x : Vector (n+1)),by
    simp only [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.property)⟩

lemma radialUnit_contMDiff (n : ℕ) (m : ℕ∞) :
    ContMDiff 𝓘(ℝ,Vector (n+1)) (𝓡 n) m (radialUnit n) := by
  let : Fact (Module.finrank ℝ (Vector (n+1))=n+1) := ⟨finrank_euclideanSpace_fin⟩
  have hr : ContMDiff 𝓘(ℝ,Vector (n+1)) 𝓘(ℝ,Vector (n+1)) m
      (fun x : punctured n => ‖(x : Vector (n+1))‖⁻¹ • (x : Vector (n+1))) := by
    intro x
    have h : ContDiffAt ℝ m (fun y : Vector (n+1) => ‖y‖⁻¹ • y) (x : Vector (n+1)) :=
      ((contDiffAt_norm ℝ x.property).inv (norm_ne_zero_iff.mpr x.property)).smul contDiffAt_id
    exact h.contMDiffAt.comp x (contMDiff_subtype_val (U := punctured n) (n := (m:ℕ∞ω))).contMDiffAt
  exact hr.codRestrict_sphere (fun x => (radialUnit n x).property)

def originBump (n : ℕ) : ContDiffBump (0 : Vector (n+1)) where
  rIn := Real.sqrt (n+1 : ℕ)/4
  rOut := Real.sqrt (n+1 : ℕ)/2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith [Real.sqrt_pos.mpr (show (0:ℝ)<(n+1 : ℕ) by positivity)]

/-- A genuine ambient function, radial near the sphere and identically zero
near the origin. The construction depends only on the intrinsic function. -/
def ambientExtension (n : ℕ) (f : RoundSphere n → ℝ) (x : Vector (n+1)) : ℝ :=
  if hx : x ≠ 0 then (1-originBump n x) * f (unitToRound n (radialUnit n ⟨x,hx⟩)) else 0

theorem ambientExtension_contDiff (n : ℕ) (m : ℕ∞) (f : RoundSphere n → ℝ)
    (hf : IntrinsicContDiff n m f) : ContDiff ℝ m (ambientExtension n f) := by
  rw [← contMDiff_iff_contDiff]
  intro x
  by_cases hx : x ≠ 0
  · have hsub : ContMDiff 𝓘(ℝ,Vector (n+1)) 𝓘(ℝ,ℝ) m
        (fun y : punctured n => ambientExtension n f (y : Vector (n+1))) := by
      have hg := hf.comp (radialUnit_contMDiff n m)
      have hc : ContMDiff 𝓘(ℝ,Vector (n+1)) 𝓘(ℝ,ℝ) m
          (fun y : punctured n => 1-originBump n (y : Vector (n+1))) :=
        (contDiff_const.sub (originBump n).contDiff).contMDiff.comp contMDiff_subtype_val
      convert hc.mul hg using 1
      funext y
      unfold ambientExtension
      split_ifs with hy
      · rfl
      · exact False.elim (hy y.property)
    exact (contMDiffAt_subtype_iff (U := punctured n) (x := ⟨x,hx⟩)).mp hsub.contMDiffAt
  · have hx0 : x=0 := not_ne_iff.mp hx
    subst x
    have hb := (originBump n).eventuallyEq_one
    have he : ambientExtension n f =ᶠ[𝓝 (0 : Vector (n+1))] (fun _ => 0) := by
      filter_upwards [hb] with x hx
      unfold ambientExtension
      split_ifs <;> simp only [hx,Pi.one_apply,sub_self,zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq he

theorem ambientExtension_restrict (n : ℕ) (f : RoundSphere n → ℝ) (x : RoundSphere n) :
    ambientExtension n f (x : Vector (n+1)) = f x := by
  have hs : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hn : ‖(x : Vector (n+1))‖ = Real.sqrt (n+1 : ℕ) := by
    exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt x.property)
  have hx : (x : Vector (n+1)) ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact hs.ne')
  have hb : originBump n (x : Vector (n+1))=0 := (originBump n).zero_of_le_dist (by
    simp only [originBump,dist_zero_right,hn]
    linarith)
  rw [ambientExtension,dite_eq_left hx,hb,sub_zero,one_mul]
  congr 1
  apply Subtype.ext
  change Real.sqrt (n+1 : ℕ) • (‖(x : Vector (n+1))‖⁻¹ • (x : Vector (n+1))) = _
  rw [hn,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]

/-- Intrinsic C¹, C², and C∞ functions all admit a global representative of
the same regularity. No ambient-extension hypothesis is required. -/
theorem exists_ambient_extension (n : ℕ) (m : ℕ∞) (f : RoundSphere n → ℝ)
    (hf : IntrinsicContDiff n m f) :
    ∃ F : Vector (n+1) → ℝ, ContDiff ℝ m F ∧ ∀ x : RoundSphere n, F x=f x :=
  ⟨ambientExtension n f,ambientExtension_contDiff n m f hf,ambientExtension_restrict n f⟩

theorem IntrinsicContDiff.of_le {n : ℕ} {m k : ℕ∞} {f : RoundSphere n → ℝ}
    (hf : IntrinsicContDiff n m f) (hkm : k ≤ m) : IntrinsicContDiff n k f := by
  change ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) k (f ∘ unitToRound n)
  exact ContMDiff.of_le hf (by exact_mod_cast hkm)

theorem IntrinsicContDiff.continuous {n : ℕ} {m : ℕ∞} {f : RoundSphere n → ℝ}
    (hf : IntrinsicContDiff n m f) : Continuous f := by
  have h := (show ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) m (f ∘ unitToRound n) from hf).continuous.comp
    (radiusDilation n).symm.continuous
  convert h using 1
  funext x
  exact congrArg f ((radiusDilation n).apply_symm_apply x).symm

theorem intrinsicContDiff_restrict (n : ℕ) (m : ℕ∞) (F : Vector (n+1) → ℝ)
    (hF : ContDiff ℝ m F) : IntrinsicContDiff n m (fun x => F x) := by
  let : Fact (Module.finrank ℝ (Vector (n+1))=n+1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContDiff ℝ m (fun x : Vector (n+1) => Real.sqrt (n+1 : ℕ) • x) :=
    by fun_prop
  exact hF.contMDiff.comp (hs.contMDiff.comp (contMDiff_coe_sphere (n := n)))

/-- The standard intrinsic definition is exactly equivalent to existence of
a global ambient representative; the forward implication is constructive. -/
theorem intrinsicContDiff_iff_exists_ambient_extension (n : ℕ) (m : ℕ∞)
    (f : RoundSphere n → ℝ) :
    IntrinsicContDiff n m f ↔
      ∃ F : Vector (n+1) → ℝ, ContDiff ℝ m F ∧ ∀ x : RoundSphere n, F x=f x := by
  constructor
  · exact exists_ambient_extension n m f
  · rintro ⟨F,hF,he⟩
    have h := intrinsicContDiff_restrict n m F hF
    have hf : (fun x : RoundSphere n => F x)=f := funext he
    rwa [hf] at h

end
end SlowEquilibration.SphericalIntrinsicExtension
