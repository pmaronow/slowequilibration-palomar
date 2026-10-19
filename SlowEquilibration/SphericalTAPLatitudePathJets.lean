-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeRadialMean

@[expose] public section

/-! Explicit dimension-scaled velocity of the actual spherical latitude
curve, for use in the conditioned second-latitude regularity theorem. -/

namespace SlowEquilibration.SphericalTAPLatitudePathJets
noncomputable section
open Set
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalForm
open SlowEquilibration.EntranceLatitudeTangentObservable
set_option autoImplicit false

def transverseLatitudeRadius (a : ℝ) : ℝ := Real.sqrt (1-a^2)

theorem transverseLatitudeRadius_contDiffOn :
    ContDiffOn ℝ 2 transverseLatitudeRadius (Ioo (-1:ℝ) 1) := by
  have hbase : ContDiffOn ℝ 2 (fun a : ℝ => 1-a^2) (Ioo (-1:ℝ) 1) := by
    fun_prop
  unfold transverseLatitudeRadius
  apply hbase.sqrt
  intro a ha
  have hp : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  exact hp.ne'

theorem transverseLatitudeRadius_hasDerivAt {a : ℝ}
    (ha : a ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt transverseLatitudeRadius
      (-a/transverseLatitudeRadius a) a := by
  have hp : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  have hd := (((hasDerivAt_id a).pow 2).const_sub 1).sqrt hp.ne'
  convert hd using 1
  · funext t
    simp [transverseLatitudeRadius]
  · simp only [transverseLatitudeRadius]
    simp only [id_eq, Pi.pow_apply, pow_one, Nat.cast_ofNat, Nat.reduceSub, mul_one]
    field_simp [(Real.sqrt_pos.mpr hp).ne']

/-- A compact latitude interval has a dimension-free scalar acceleration
constant. Its construction uses only smoothness of `sqrt(1-a²)` in the
interior, without a stochastic or model-dependent assumption. -/
theorem transverseLatitudeRadius_second_uniform
    {r : ℝ} (hr1 : r < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ Icc (-r) r,
      |iteratedDeriv 2 transverseLatitudeRadius a| ≤ B := by
  have hsub : Icc (-r) r ⊆ Ioo (-1:ℝ) 1 := by
    intro a ha
    constructor <;> linarith [ha.1,ha.2,hr1]
  have hcontOpen : ContinuousOn (iteratedDeriv 2 transverseLatitudeRadius)
      (Ioo (-1:ℝ) 1) := by
    have h := transverseLatitudeRadius_contDiffOn.continuousOn_iteratedDerivWithin
      (m := 2) (by norm_num) isOpen_Ioo.uniqueDiffOn
    exact h.congr (fun a ha =>
      (iteratedDerivWithin_of_isOpen isOpen_Ioo ha).symm)
  have hcont : ContinuousOn
      (fun a => |iteratedDeriv 2 transverseLatitudeRadius a|)
      (Icc (-r) r) := (hcontOpen.mono hsub).abs
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro a ha
  exact (hB ⟨a, ha, rfl⟩).trans (le_max_left _ _)

/-- Any closed latitude interval inside the two poles fits in a symmetric
compact strip, so the uniform curvature constants apply to the manuscript's
arbitrary compact interval. -/
theorem compactLatitudeInterval_symmetric_strip
    {lo hi : ℝ} (hlo : -1 < lo) (hlohi : lo ≤ hi) (hhi : hi < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ Icc lo hi ⊆ Icc (-r) r := by
  let r := max |lo| |hi|
  have hlo1 : lo < 1 := lt_of_le_of_lt hlohi hhi
  have hhi1 : -1 < hi := lt_of_lt_of_le hlo hlohi
  refine ⟨r, le_max_of_le_left (abs_nonneg lo), ?_, ?_⟩
  · exact max_lt (abs_lt.mpr ⟨hlo, hlo1⟩)
      (abs_lt.mpr ⟨hhi1, hhi⟩)
  · intro a ha
    have hloa : -|lo| ≤ a := (neg_abs_le lo).trans ha.1
    have hahi : a ≤ |hi| := ha.2.trans (le_abs_self hi)
    exact ⟨(neg_le_neg (le_max_left |lo| |hi|)).trans hloa,
      hahi.trans (le_max_right |lo| |hi|)⟩

def physicalLatitudePoint {N : ℕ} (u ω : Vector N) (a : ℝ) : Vector N :=
  a • u + transverseLatitudeRadius a • ω

theorem latitudeMap_eq_physicalLatitudePoint {n : ℕ}
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (x : Vector n) (a : ℝ) :
    latitudeMap u e a x = physicalLatitudePoint u
      (Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e x) a := by
  unfold latitudeMap physicalLatitudePoint transverseLatitudeRadius
  rw [Real.sqrt_mul (by positivity : 0 ≤ (((n+1:ℕ):ℝ)/(n:ℝ))), smul_smul]
  rw [mul_comm (Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)))]

theorem latitudeMap_transverse_norm {n : ℕ} (hn : 1 ≤ n)
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (x : Vector n)
    (hx : ‖x‖^2 = (n:ℝ)) :
    ‖Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e x‖ =
      Real.sqrt ((n+1:ℕ):ℝ) := by
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsq :
      ‖Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e x‖^2 = ((n+1:ℕ):ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (div_nonneg (by positivity) hn0.le), e.norm_map, hx]
    field_simp
  calc
    _ = Real.sqrt (‖Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e x‖^2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := by rw [hsq]

theorem physicalLatitudePoint_contDiffAt {N : ℕ}
    (u ω : Vector N) {a : ℝ} (ha : a ∈ Ioo (-1:ℝ) 1) :
    ContDiffAt ℝ 2 (physicalLatitudePoint u ω) a := by
  have hq : ContDiffAt ℝ 2 transverseLatitudeRadius a :=
    transverseLatitudeRadius_contDiffOn.contDiffAt (isOpen_Ioo.mem_nhds ha)
  unfold physicalLatitudePoint
  fun_prop

theorem physicalLatitudePoint_second_derivative {N : ℕ}
    (u ω : Vector N) {a : ℝ} (ha : a ∈ Ioo (-1:ℝ) 1) :
    iteratedDeriv 2 (physicalLatitudePoint u ω) a =
      iteratedDeriv 2 transverseLatitudeRadius a • ω := by
  have hq : ContDiffAt ℝ 2 transverseLatitudeRadius a :=
    transverseLatitudeRadius_contDiffOn.contDiffAt (isOpen_Ioo.mem_nhds ha)
  have hlin : ContDiffAt ℝ 2 (fun t : ℝ => t • u) a := by fun_prop
  have hquad : ContDiffAt ℝ 2 (fun t : ℝ => transverseLatitudeRadius t • ω) a :=
    hq.smul_const ω
  have hadd := iteratedDeriv_fun_add hlin hquad
  change iteratedDeriv 2 (physicalLatitudePoint u ω) a = _ at hadd
  rw [hadd]
  have hlinzero : iteratedDeriv 2 (fun t : ℝ => t • u) a = 0 := by
    rw [iteratedDeriv_smul_const (show ContDiffAt ℝ 2 (fun t : ℝ => t) a by fun_prop)]
    simp [iteratedDeriv_fun_id]
  rw [hlinzero, zero_add, iteratedDeriv_smul_const hq]

theorem physicalLatitudePoint_acceleration_bound {N : ℕ}
    (u ω : Vector N) {a r B : ℝ} (ha : a ∈ Icc (-r) r)
    (hr1 : r < 1) (hω : ‖ω‖ ≤ Real.sqrt (N : ℝ))
    (hB : ∀ t ∈ Icc (-r) r,
      |iteratedDeriv 2 transverseLatitudeRadius t| ≤ B) :
    ‖iteratedDeriv 2 (physicalLatitudePoint u ω) a‖ ≤
      B * Real.sqrt (N : ℝ) := by
  have haopen : a ∈ Ioo (-1:ℝ) 1 := by
    constructor <;> linarith [ha.1,ha.2,hr1]
  rw [physicalLatitudePoint_second_derivative u ω haopen, norm_smul, Real.norm_eq_abs]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a ha)
  exact mul_le_mul (hB a ha) hω (norm_nonneg _) hB0

theorem latitudeMap_acceleration_bound {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (x : Vector n) (hx : ‖x‖^2 = (n:ℝ))
    {a r B : ℝ} (ha : a ∈ Icc (-r) r) (hr1 : r < 1)
    (hB : ∀ t ∈ Icc (-r) r,
      |iteratedDeriv 2 transverseLatitudeRadius t| ≤ B) :
    ‖iteratedDeriv 2 (fun t => latitudeMap u e t x) a‖ ≤
      B * Real.sqrt ((n+1:ℕ):ℝ) := by
  have hfun : (fun t => latitudeMap u e t x) =
      physicalLatitudePoint u
        (Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • e x) := by
    funext t
    exact latitudeMap_eq_physicalLatitudePoint u e x t
  rw [hfun]
  exact physicalLatitudePoint_acceleration_bound u _ ha hr1
    (latitudeMap_transverse_norm hn e x hx).le hB

theorem physicalLatitudeMap_speed_bound {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (he : ∀ y, inner ℝ (e y) u = 0)
    (x : Vector n) (hx : ‖x‖^2 = (n:ℝ))
    {a r : ℝ} (ha : a ∈ Ioo (-1:ℝ) 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (har : |a| ≤ r) :
    ‖deriv (fun t => latitudeMap u e t x) a‖ ≤
      Real.sqrt ((n+1:ℕ):ℝ)/(1-r^2) := by
  have hN : 0 < n+1 := by omega
  have hp := latitudeMap_norm_sq hn u hu e he (abs_lt.mpr ha).le x hx
  have hOn : SphericalAging.HardSphereDynamics.OnSphere (latitudeMap u e a x) := by
    change inner ℝ (latitudeMap u e a x) (latitudeMap u e a x) = (n+1:ℕ)
    rwa [real_inner_self_eq_norm_sq]
  have hproj : ‖tangentProjection (latitudeMap u e a x) u‖ ≤ ‖u‖ := by
    have hnorm := SphericalForm.tangentProjection_norm_le
      (by omega : n+1 ≠ 0) (latitudeMap u e a x) hOn
    exact ((tangentProjection (latitudeMap u e a x)).le_opNorm u).trans
      (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  have hunorm : ‖u‖ = Real.sqrt ((n+1:ℕ):ℝ) :=
    SphericalAging.LandscapeDerivatives.sphere_norm u hu
  have hden : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  have hdenr : 0 < 1-r^2 := by nlinarith [hr0,hr1]
  have hrpow : a^2 ≤ r^2 := by nlinarith [abs_le.mp har]
  rw [(latitudeMap_radial_hasDerivAt hn u hu e he ha x).deriv,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hden]
  calc
    _ ≤ (1-a^2)⁻¹ * ‖u‖ :=
      mul_le_mul_of_nonneg_left hproj (inv_nonneg.mpr hden.le)
    _ = Real.sqrt ((n+1:ℕ):ℝ)/(1-a^2) := by rw [hunorm]; ring
    _ ≤ Real.sqrt ((n+1:ℕ):ℝ)/(1-r^2) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hdenr (by linarith)

end
end SlowEquilibration.SphericalTAPLatitudePathJets
