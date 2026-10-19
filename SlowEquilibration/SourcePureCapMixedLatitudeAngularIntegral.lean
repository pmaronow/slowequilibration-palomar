-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapCrossAngularBound
public import SlowEquilibration.SphericalCentralOverlapPerturbation

/-! The source transverse angular estimate transported to the product of
two true physical latitude laws at independently varying cap latitudes. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapMixedLatitudeAngularIntegral
noncomputable section
open Set Filter MeasureTheory
open SphericalModel PureStationarity
open SourcePureCapCrossAngularBound
open SourcePureCapPosteriorCrossKernel
open SourcePureCapMixedLatitudeOverlap
set_option autoImplicit false
set_option maxHeartbeats 1000000

def pureCrossPairWeight (n p : ℕ) (hp : 2 ≤ p) (β q₁ q₂ : ℝ)
    (z : Vector (n+1) × Vector (n+1)) : ℝ :=
  Real.exp (((n+1 : ℕ) : ℝ)*β^2*
    sourceValueTauCross (FiniteMixture.pure p hp 1 (by positivity))
      1 q₁ q₂ (overlap z.1 z.2-q₁*q₂))

theorem pureCrossPairWeight_continuous (n p : ℕ) (hp : 2 ≤ p)
    (β q₁ q₂ : ℝ) : Continuous (pureCrossPairWeight n p hp β q₁ q₂) := by
  unfold pureCrossPairWeight
  simp only [sourceValueTauCross_pure p hp 1 (by positivity)
    (by norm_num : (0 : ℝ) < 1)]
  unfold overlap
  fun_prop

/-- Uniform bound under the physical product of two normalized latitude
laws, before radial coarea is integrated. -/
theorem pure_source_mixed_latitude_angular_integral_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2 = ((n+1 : ℕ) : ℝ) →
      ∀ q₁ ∈ Ico a 1, ∀ q₂ ∈ Ico a 1,
      (∫ z : Vector (n+1) × Vector (n+1),
        pureCrossPairWeight n p hp β q₁ q₂ z
          ∂(latitudeLaw u (latitudeFrameAt u) q₁).prod
            (latitudeLaw u (latitudeFrameAt u) q₂)) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := pure_source_cross_angular_exponential_bound
    p hp β ha hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop 1] with n hbound hn
  intro u hu q₁ hq₁ q₂ hq₂
  let e := latitudeFrameAt u
  have he : ∀ x, inner ℝ (e x) u=0 := latitudeFrameAt_orthogonal u hu
  have hq₁abs : |q₁| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1,hq₁.1],hq₁.2.le⟩
  have hq₂abs : |q₂| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1,hq₂.1],hq₂.2.le⟩
  let T : Vector n × Vector n → Vector (n+1) × Vector (n+1) :=
    Prod.map (latitudeMap u e q₁) (latitudeMap u e q₂)
  have hT : Continuous T :=
    (latitudeMap_continuous u e q₁).prodMap (latitudeMap_continuous u e q₂)
  have hF := pureCrossPairWeight_continuous n p hp β q₁ q₂
  have hcomp : Integrable (pureCrossPairWeight n p hp β q₁ q₂ ∘ T)
      ((sphereLaw n).prod (sphereLaw n)) :=
    (memLp_spherePair_continuous hn (hF.comp hT) 1).integrable le_rfl
  have heq (z : Vector n × Vector n) :
      pureCrossPairWeight n p hp β q₁ q₂ (T z) =
      Real.exp (((n+1 : ℕ) : ℝ)*β^2*
        sourceValueTauCross (FiniteMixture.pure p hp 1 (by positivity))
          1 q₁ q₂
          (Real.sqrt (1-q₁^2)*Real.sqrt (1-q₂^2)*overlap z.1 z.2)) := by
    unfold pureCrossPairWeight T
    simp only [Prod.map_fst,Prod.map_snd]
    rw [overlap_latitude_pair_mixed hn u hu e he hq₁abs hq₂abs]
    simp only [add_sub_cancel_left]
  have hbound' : ∀ᵐ x : Vector n ∂sphereLaw n,
      (∫ y : Vector n, pureCrossPairWeight n p hp β q₁ q₂ (T (x,y))
        ∂sphereLaw n) ≤ C := by
    filter_upwards [sphereLaw_support hn] with x hx
    simpa only [heq] using hbound x hx q₁ hq₁ q₂ hq₂
  have houter : Integrable (fun x : Vector n =>
      ∫ y : Vector n, pureCrossPairWeight n p hp β q₁ q₂ (T (x,y))
        ∂sphereLaw n) (sphereLaw n) := hcomp.integral_prod_left
  calc
    _ = ∫ z : Vector n × Vector n,
        pureCrossPairWeight n p hp β q₁ q₂ (T z)
        ∂(sphereLaw n).prod (sphereLaw n) := by
      unfold latitudeLaw
      rw [Measure.map_prod_map _ _
        (latitudeMap_continuous u e q₁).measurable
        (latitudeMap_continuous u e q₂).measurable]
      exact integral_map hT.measurable.aemeasurable hF.aestronglyMeasurable
    _ = ∫ x : Vector n, (∫ y : Vector n,
        pureCrossPairWeight n p hp β q₁ q₂ (T (x,y)) ∂sphereLaw n)
        ∂sphereLaw n := integral_prod _ hcomp
    _ ≤ ∫ _x : Vector n, C ∂sphereLaw n := by
      apply integral_mono_ae houter (integrable_const C)
      exact hbound'
    _ = C := by simp

end
end SlowEquilibration.SourcePureCapMixedLatitudeAngularIntegral
