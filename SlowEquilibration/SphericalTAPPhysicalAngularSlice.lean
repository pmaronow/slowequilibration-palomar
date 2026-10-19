-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPhysicalShellLower
public import SlowEquilibration.SphericalLatitudeLaplace
public import SlowEquilibration.SphericalLatitudeRegularity
public import SlowEquilibration.SphereSupportedIntegrals

@[expose] public section

/-! The actual normalized transverse `sphereLaw n` in every physical
tangent frame. Its central exponential integral is identified with the
original Hamiltonian's exact latitude density partition. -/

namespace SlowEquilibration.SphericalTAPPhysicalAngularSlice
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalTAPPhysicalLatitudeSlice
open SlowEquilibration.SphericalTAPPhysicalShellLower
open SlowEquilibration.SphericalTAPLatitudeEntropyCurvature
set_option autoImplicit false

/-- A point on the physical transverse sphere in the frame at `u`. -/
def physicalTransverseAt (n : ℕ) (u : Vector (n+1)) (x : Vector n) :
    Vector (n+1) :=
  Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • latitudeFrameAt u x

theorem latitudeMap_eq_physicalSlicePoint_at
    (n : ℕ) (hn : 1 ≤ n) (u : Vector (n+1))
    (a : ℝ) (_ha : |a| ≤ 1) (x : Vector n) :
    latitudeMap u (latitudeFrameAt u) a x =
      a • u + Real.sqrt (1-a^2) • physicalTransverseAt n u x := by
  have hratio : 0 ≤ (((n+1:ℕ):ℝ)/(n:ℝ)) := by positivity
  simp only [latitudeMap, physicalTransverseAt, smul_smul]
  rw [Real.sqrt_mul hratio]
  ring

theorem physicalLatitudeSlice_eq_originalLatitudeField_at
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    (a : ℝ) (ha : |a| ≤ 1) (x : Vector n) :
    physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J a =
      field (mixtureCoefficients μ) J
        (latitudeMap u (latitudeFrameAt u) a x) := by
  unfold physicalLatitudeSlice
  rw [latitudeMap_eq_physicalSlicePoint_at n hn u a ha x]

/-- The entropy exponential is exactly the source coarea weight. -/
theorem physicalEntropy_exp_eq_sqrt_pow
    (n : ℕ) (a : ℝ) (ha : a ∈ Ioo (-1:ℝ) 1) :
    Real.exp ((((n-2:ℕ):ℝ)/2)*Real.log (1-a^2)) =
      (Real.sqrt (1-a^2))^(n-2) := by
  have hp : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  have hs : 0 < Real.sqrt (1-a^2) := Real.sqrt_pos.mpr hp
  rw [show (((n-2:ℕ):ℝ)/2)*Real.log (1-a^2) =
      ((n-2:ℕ):ℝ)*(Real.log (1-a^2)/2) by ring,
    ← Real.log_sqrt hp.le]
  rw [Real.exp_nat_mul,Real.exp_log hs]

/-- The central angular integral is the literal original-field latitude
density, with ambient entropy coefficient `(N-3)/2`. -/
theorem physicalAngularExponent_integral_eq_latitudeDensity
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    (β a : ℝ) (ha : a ∈ Ioo (-1:ℝ) 1) :
    (∫ x : Vector n,
      Real.exp (physicalLatitudeExponent n μ u
        (physicalTransverseAt n u x) J β a) ∂sphereLaw n) =
      latitudeDensityPartition n β (field (mixtureCoefficients μ) J) u a := by
  have habs : |a| ≤ 1 := abs_le.mpr ⟨ha.1.le,ha.2.le⟩
  have hpoint (x : Vector n) :
      Real.exp (physicalLatitudeExponent n μ u
        (physicalTransverseAt n u x) J β a) =
      Real.exp ((((n-2:ℕ):ℝ)/2)*Real.log (1-a^2)) *
        Real.exp (β*field (mixtureCoefficients μ) J
          (latitudeMap u (latitudeFrameAt u) a x)) := by
    rw [show physicalLatitudeExponent n μ u (physicalTransverseAt n u x) J β a =
        β*field (mixtureCoefficients μ) J
          (latitudeMap u (latitudeFrameAt u) a x) +
          (((n-2:ℕ):ℝ)/2)*Real.log (1-a^2) by
          unfold physicalLatitudeExponent latitudeExponent baseEntropy
          rw [physicalLatitudeSlice_eq_originalLatitudeField_at n hn μ u J a habs x]]
    rw [show β*field (mixtureCoefficients μ) J
        (latitudeMap u (latitudeFrameAt u) a x)+
        (((n-2:ℕ):ℝ)/2)*Real.log (1-a^2) =
        (((n-2:ℕ):ℝ)/2)*Real.log (1-a^2)+
        β*field (mixtureCoefficients μ) J
          (latitudeMap u (latitudeFrameAt u) a x) by ring, Real.exp_add]
  simp_rw [hpoint]
  rw [integral_const_mul, physicalEntropy_exp_eq_sqrt_pow n a ha]
  unfold latitudeDensityPartition
  rw [latitudePartition_eq_sphereIntegral]

/-- The central angular exponential is integrable on the actual compact
transverse sphere for every fixed latitude. -/
theorem physicalAngularExponent_integrable
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    (β a : ℝ) :
    Integrable (fun x : Vector n =>
      Real.exp (physicalLatitudeExponent n μ u
        (physicalTransverseAt n u x) J β a)) (sphereLaw n) := by
  have hf := (field_contDiff (mixtureCoefficients μ) J).continuous
  have hc : Continuous (fun x : Vector n =>
      Real.exp (physicalLatitudeExponent n μ u
        (physicalTransverseAt n u x) J β a)) := by
    unfold physicalLatitudeExponent latitudeExponent baseEntropy
      physicalLatitudeSlice physicalTransverseAt
    fun_prop
  exact SphericalForm.integrable_sphereSupported_continuous (sphereLaw n)
    (sphereLaw_support hn) hc

/-- Symmetric latitude averaging under the actual transverse sphere law
at an arbitrary physical center. The left side is now the exact central
latitude density of the original Hamiltonian. -/
theorem physicalAngularShell_lower
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    {r center width β C₀ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hwidth : 0 < width)
    (hβ : 0 ≤ β) (hC₀ : 0 ≤ C₀)
    (hinside : ∀ a ∈ Icc (center-width) (center+width), |a| ≤ r)
    (hfield : ∀ x a, a ∈ Icc (center-width) (center+width) →
      |iteratedDeriv 2
        (physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J) a| ≤
        C₀*((n+1:ℕ):ℝ))
    (hcentral : Integrable (fun x : Vector n =>
      Real.exp (physicalLatitudeExponent n μ u
        (physicalTransverseAt n u x) J β center)) (sphereLaw n))
    (hshell : Integrable (fun x : Vector n =>
      ∫ a in (center-width)..(center+width),
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a)) (sphereLaw n)) :
    (2*width*Real.exp (-(((n+1:ℕ):ℝ)*
      (β*C₀+2/(1-r^2)^2))*width^2/2))*
      latitudeDensityPartition n β (field (mixtureCoefficients μ) J) u center ≤
        ∫ x : Vector n, (∫ a in (center-width)..(center+width),
          Real.exp (physicalLatitudeExponent n μ u
            (physicalTransverseAt n u x) J β a)) ∂sphereLaw n := by
  have hcenter : center ∈ Icc (center-width) (center+width) := by
    constructor <;> linarith [hwidth]
  have hc : center ∈ Ioo (-1:ℝ) 1 := by
    have habs := hinside center hcenter
    rw [abs_le] at habs
    constructor <;> linarith [habs.1,habs.2,hr1]
  have h := physicalLatitudeExponent_shell_lower (sphereLaw n) n hn μ u
    (physicalTransverseAt n u) J hr0 hr1 hwidth hβ hC₀
    hinside hfield hcentral hshell
  rw [physicalAngularExponent_integral_eq_latitudeDensity n (by omega) μ u J β center hc] at h
  exact h

/-- The source curvature event is needed only on the physical transverse
sphere, because the angular average uses `sphereLaw n`. -/
theorem physicalAngularShell_lower_supported
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    {r center width β C₀ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hwidth : 0 < width)
    (hβ : 0 ≤ β) (_hC₀ : 0 ≤ C₀)
    (hinside : ∀ a ∈ Icc (center-width) (center+width), |a| ≤ r)
    (hfield : ∀ x : Vector n, ‖x‖^2=(n:ℝ) → ∀ a,
      a ∈ Icc (center-width) (center+width) →
      |iteratedDeriv 2
        (physicalLatitudeSlice n μ u (physicalTransverseAt n u x) J) a| ≤
        C₀*((n+1:ℕ):ℝ))
    (hcentral : Integrable (fun x : Vector n =>
      Real.exp (physicalLatitudeExponent n μ u
        (physicalTransverseAt n u x) J β center)) (sphereLaw n))
    (hshell : Integrable (fun x : Vector n =>
      ∫ a in (center-width)..(center+width),
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a)) (sphereLaw n)) :
    (2*width*Real.exp (-(((n+1:ℕ):ℝ)*
      (β*C₀+2/(1-r^2)^2))*width^2/2))*
      latitudeDensityPartition n β (field (mixtureCoefficients μ) J) u center ≤
        ∫ x : Vector n, (∫ a in (center-width)..(center+width),
          Real.exp (physicalLatitudeExponent n μ u
            (physicalTransverseAt n u x) J β a)) ∂sphereLaw n := by
  let curvature : ℝ := ((n+1:ℕ):ℝ)*(β*C₀+2/(1-r^2)^2)
  let c : ℝ := 2*width*Real.exp (-curvature*width^2/2)
  have hpoint : ∀ᵐ x : Vector n ∂sphereLaw n,
      c*Real.exp (physicalLatitudeExponent n μ u
        (physicalTransverseAt n u x) J β center) ≤
        ∫ a in (center-width)..(center+width),
          Real.exp (physicalLatitudeExponent n μ u
            (physicalTransverseAt n u x) J β a) := by
    filter_upwards [sphereLaw_support (by omega : 1 ≤ n)] with x hx
    have h := physicalLatitudeExponent_symmetric_integral_lower
      n hn μ u (physicalTransverseAt n u x) J hr0 hr1 hwidth hβ
      hinside (hfield x hx)
    have heq : 2*width*Real.exp
        (physicalLatitudeExponent n μ u (physicalTransverseAt n u x) J β center-
          curvature*width^2/2) =
        c*Real.exp
          (physicalLatitudeExponent n μ u (physicalTransverseAt n u x) J β center) := by
      dsimp [c]
      rw [show physicalLatitudeExponent n μ u (physicalTransverseAt n u x) J β center-
          curvature*width^2/2 = -curvature*width^2/2 +
            physicalLatitudeExponent n μ u (physicalTransverseAt n u x) J β center
          by ring, Real.exp_add]
      ring
    rw [heq] at h
    exact h
  have hbound := integral_mono_ae (hcentral.const_mul c) hshell hpoint
  rw [integral_const_mul] at hbound
  have hcenter : center ∈ Icc (center-width) (center+width) := by
    constructor <;> linarith [hwidth]
  have hc : center ∈ Ioo (-1:ℝ) 1 := by
    have habs := hinside center hcenter
    rw [abs_le] at habs
    constructor <;> linarith [habs.1,habs.2,hr1]
  rw [physicalAngularExponent_integral_eq_latitudeDensity n (by omega)
    μ u J β center hc] at hbound
  simpa only [c, curvature] using hbound

/-- Fubini identifies the physical angular shell integral with the
manuscript's exact latitude density integral. The joint integrability
condition is the standard analytic side condition for real-valued Fubini. -/
theorem physicalAngularBand_integral_eq_density
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (J : Disorder (n+1) μ.maxDegree)
    (β center width : ℝ) (hwidth : 0 ≤ width)
    (hbelow : -1 < center-width) (habove : center+width < 1)
    (hjoint : Integrable
      (Function.uncurry (fun a (x : Vector n) =>
        Real.exp (physicalLatitudeExponent n μ u
          (physicalTransverseAt n u x) J β a)))
      ((volume.restrict (Icc (center-width) (center+width))).prod (sphereLaw n))) :
    (∫ x : Vector n, (∫ a in (center-width)..(center+width),
      Real.exp (physicalLatitudeExponent n μ u
        (physicalTransverseAt n u x) J β a)) ∂sphereLaw n) =
    ∫ a in Icc (center-width) (center+width),
      latitudeDensityPartition n β (field (mixtureCoefficients μ) J) u a
      ∂volume := by
  have horder : center-width ≤ center+width := by linarith
  have hswap := integral_integral_swap hjoint
  calc
    _ = ∫ x : Vector n, (∫ a in Icc (center-width) (center+width),
          Real.exp (physicalLatitudeExponent n μ u
            (physicalTransverseAt n u x) J β a) ∂volume) ∂sphereLaw n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          dsimp
          rw [intervalIntegral.integral_of_le horder,
            ← integral_Icc_eq_integral_Ioc])
    _ = ∫ a in Icc (center-width) (center+width),
          (∫ x : Vector n,
            Real.exp (physicalLatitudeExponent n μ u
              (physicalTransverseAt n u x) J β a) ∂sphereLaw n) ∂volume := hswap.symm
    _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
        exact physicalAngularExponent_integral_eq_latitudeDensity n hn μ u J β a
          ⟨lt_of_lt_of_le hbelow ha.1, lt_of_le_of_lt ha.2 habove⟩

end
end SlowEquilibration.SphericalTAPPhysicalAngularSlice
