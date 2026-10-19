-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPSymmetricLatitudeIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! The exact second derivative and a uniform interior lower bound for the
spherical coarea entropy `(N-3)/2 * log (1-a²)`. This supplies the deterministic
entropy part of the curvature condition in manuscript Lemma 12.19. -/

namespace SlowEquilibration.SphericalTAPLatitudeEntropyCurvature
noncomputable section
open Set
open scoped Topology
set_option autoImplicit false

def baseEntropy (a : ℝ) : ℝ := Real.log (1-a^2)

theorem baseEntropy_contDiffOn :
    ContDiffOn ℝ 2 baseEntropy (Ioo (-1:ℝ) 1) := by
  unfold baseEntropy
  apply ContDiffOn.log (by fun_prop)
  intro a ha
  have hp : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  exact hp.ne'

theorem baseEntropy_deriv {a : ℝ} (ha : a ∈ Ioo (-1:ℝ) 1) :
    deriv baseEntropy a = -2*a/(1-a^2) := by
  have hp : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  have hf : HasDerivAt (fun y : ℝ => 1-y^2) (-2*a) a := by
    convert (hasDerivAt_const a (1:ℝ)).sub ((hasDerivAt_id a).pow 2) using 1
    · funext y; simp
    · simp
  unfold baseEntropy
  convert (hf.log hp.ne').deriv using 1

theorem baseEntropy_second_deriv {a : ℝ} (ha : a ∈ Ioo (-1:ℝ) 1) :
    iteratedDeriv 2 baseEntropy a = -2*(1+a^2)/(1-a^2)^2 := by
  have hp : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  rw [show (2:ℕ)=1+1 by norm_num,iteratedDeriv_succ',iteratedDeriv_one]
  have hlocal : deriv baseEntropy =ᶠ[𝓝 a] (fun y : ℝ => -2*y/(1-y^2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with y hy
    exact baseEntropy_deriv hy
  rw [Filter.EventuallyEq.deriv_eq hlocal]
  have hf : HasDerivAt (fun y : ℝ => -2*y) (-2) a := by
    convert (hasDerivAt_const a (-2:ℝ)).mul (hasDerivAt_id a) using 1
    · funext y; simp
    · simp
  have hg : HasDerivAt (fun y : ℝ => 1-y^2) (-2*a) a := by
    convert (hasDerivAt_const a (1:ℝ)).sub ((hasDerivAt_id a).pow 2) using 1
    · funext y; simp
    · simp
  convert (hf.div hg hp.ne').deriv using 1
  field_simp [hp.ne']
  ring

/-- The entropy curvature is bounded uniformly on an interior latitude
interval, with an explicit constant that diverges only at the poles. -/
theorem baseEntropy_second_deriv_lower {r a : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : |a| ≤ r) :
    -4/(1-r^2)^2 ≤ iteratedDeriv 2 baseEntropy a := by
  have hasq : a^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hr0).mpr ha
  have haI : a ∈ Ioo (-1:ℝ) 1 := by
    rw [abs_le] at ha
    constructor <;> nlinarith [ha.1,ha.2,hr1]
  have hrpos : 0 < 1-r^2 := by nlinarith
  have hap : 0 < 1-a^2 := by nlinarith
  have hden : (1-r^2)^2 ≤ (1-a^2)^2 := by nlinarith
  have hnum : 1+a^2 ≤ 2 := by nlinarith
  have hh : 2*(1+a^2)*(1-r^2)^2 ≤ 4*(1-a^2)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2-(1+a^2) by linarith)
      (sq_nonneg (1-r^2))]
  rw [baseEntropy_second_deriv haI]
  apply (div_le_div_iff₀ (sq_pos_of_pos hrpos) (sq_pos_of_pos hap)).mpr
  nlinarith [hh]

/-- The source entropy coefficient `(N-3)/2` contributes at most a fixed
multiple of `N` to the negative second derivative on any fixed band. -/
theorem scaledEntropy_second_deriv_lower {r a m N : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : |a| ≤ r)
    (hm : 0 ≤ m) (hmN : m ≤ N) :
    -N*(2/(1-r^2)^2) ≤
      iteratedDeriv 2 (fun x => (m/2)*baseEntropy x) a := by
  have hrpos : 0 < 1-r^2 := by nlinarith
  have hcurv := baseEntropy_second_deriv_lower hr0 hr1 ha
  have hmhalf : 0 ≤ m/2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcurv hmhalf
  have hN := mul_le_mul_of_nonneg_right hmN
    (show 0 ≤ 2/(1-r^2)^2 by positivity)
  rw [show (fun x => (m/2)*baseEntropy x) = (m/2) • baseEntropy by rfl,
    iteratedDeriv_const_smul_field] 
  simp only [smul_eq_mul]
  calc
    -N*(2/(1-r^2)^2) ≤ -m*(2/(1-r^2)^2) := by nlinarith [hN]
    _ = m/2*(-4/(1-r^2)^2) := by ring
    _ ≤ m/2*iteratedDeriv 2 baseEntropy a := hmul

/-- The actual source latitude exponent separates into the Hamiltonian
slice and the spherical entropy density. -/
def latitudeExponent (f : ℝ → ℝ) (β m : ℝ) (a : ℝ) : ℝ :=
  β*f a+(m/2)*baseEntropy a

theorem latitudeExponent_contDiffOn (f : ℝ → ℝ) (β m : ℝ)
    (hf : ContDiffOn ℝ 2 f (Ioo (-1:ℝ) 1)) :
    ContDiffOn ℝ 2 (latitudeExponent f β m) (Ioo (-1:ℝ) 1) := by
  unfold latitudeExponent
  exact (ContDiffOn.const_smul β hf).add
    (ContDiffOn.const_smul (m/2) baseEntropy_contDiffOn)

/-- A source `O(N)` Hamiltonian second-derivative bound and the exact
coarea entropy yield the `O(N)` curvature bound used by the symmetric
latitude argument. -/
theorem latitudeExponent_second_deriv_lower
    {f : ℝ → ℝ} {r a β m N C₀ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo (-1:ℝ) 1))
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ha : |a| ≤ r)
    (hβ : 0 ≤ β)
    (hm : 0 ≤ m) (hmN : m ≤ N)
    (hfield : |iteratedDeriv 2 f a| ≤ C₀*N) :
    -N*(β*C₀+2/(1-r^2)^2) ≤
      iteratedDeriv 2 (latitudeExponent f β m) a := by
  have haI : a ∈ Ioo (-1:ℝ) 1 := by
    rw [abs_le] at ha
    constructor <;> nlinarith [ha.1,ha.2,hr1]
  have hfAt : ContDiffAt ℝ 2 f a :=
    hf.contDiffAt (isOpen_Ioo.mem_nhds haI)
  have heAt : ContDiffAt ℝ 2 baseEntropy a :=
    baseEntropy_contDiffOn.contDiffAt (isOpen_Ioo.mem_nhds haI)
  have hderiv :
      iteratedDeriv 2 (latitudeExponent f β m) a =
      β*iteratedDeriv 2 f a+(m/2)*iteratedDeriv 2 baseEntropy a := by
    unfold latitudeExponent
    change iteratedDeriv 2 (fun x => β • f x+(m/2) • baseEntropy x) a = _
    rw [iteratedDeriv_fun_add (ContDiffAt.const_smul β hfAt)
      (ContDiffAt.const_smul (m/2) heAt),
      iteratedDeriv_fun_const_smul_field,iteratedDeriv_fun_const_smul_field]
    simp only [smul_eq_mul]
  have hfieldLower : -C₀*N ≤ iteratedDeriv 2 f a := by
    nlinarith [neg_le_of_abs_le hfield]
  have hfieldScaled : β*(-C₀*N) ≤ β*iteratedDeriv 2 f a :=
    mul_le_mul_of_nonneg_left hfieldLower hβ
  have hent := scaledEntropy_second_deriv_lower hr0 hr1 ha hm hmN
  change -N*(2/(1-r^2)^2) ≤ iteratedDeriv 2 ((m/2) • baseEntropy) a at hent
  rw [iteratedDeriv_const_smul_field] at hent
  simp only [smul_eq_mul] at hent
  rw [hderiv]
  nlinarith [hfieldScaled,hent]

end
end SlowEquilibration.SphericalTAPLatitudeEntropyCurvature
