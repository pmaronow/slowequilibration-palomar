module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterEnergy
public import SlowEquilibration.SphericalBarycenterProfile
public import SlowEquilibration.SphericalBarycenterQuantitativeAlignment
public import SlowEquilibration.ExponentialEnergyAbsorption

@[expose] public section

/-! # The actual overlap-weighted observable used in the memory proof

The cutoff and the Gibbs observable are explicitly constructed. The source
cap and collar mass exponents yield the exact finite-dimensional energy and
alignment estimates. No small-energy or aligned-observable premise replaces
this construction.
-/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {N : ℕ}

/-- The source choice, with exactly one unit of excess suppression. -/
def sourceK (J δ : ℝ) : ℝ := (J+2*δ+1)/2

/-- The explicit global smooth cutoff used to construct the observable. -/
def sourceProfile (J δ q₁ q₂ : ℝ) : ℝ → ℝ := profile (sourceK J δ) q₁ q₂

/-- The literal normalized, overlap-weighted Gibbs spin mean. -/
def sourceObservable (β : ℝ) (H : Vector N → ℝ) (J δ q₁ q₂ : ℝ) :
    Vector N → Vector N := barycenter β H (sourceProfile J δ q₁ q₂)

lemma sourceK_gap (J δ : ℝ) : 2*sourceK J δ-(J+2*δ)=1 := by
  unfold sourceK
  ring

lemma sourceProfile_contDiff (J δ q₁ q₂ : ℝ) :
    ContDiff ℝ ∞ (sourceProfile J δ q₁ q₂) := profile_contDiff _ _ _

lemma sourceObservable_contDiff (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (J δ q₁ q₂ : ℝ) :
    ContDiff ℝ ∞ (sourceObservable β H J δ q₁ q₂) :=
  barycenter_contDiff hN β hH (sourceProfile_contDiff _ _ _ _)

lemma sourceObservable_norm_le_one (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (J δ q₁ q₂ : ℝ) (x : Vector N) :
    ‖sourceObservable β H J δ q₁ q₂ x‖ ≤ 1 :=
  barycenter_norm_le_one hN β hH (sourceProfile_contDiff _ _ _ _) x

/-- The cap lower bound and collar upper bound have the literal source
ratio exponent `G - 4δ` after normalization by the true denominator. -/
theorem source_collar_ratio_le (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (J G δ q₁ q₂ : ℝ) (hq : q₁ < q₂)
    (x : Vector N) (hx : OnSphere x)
    (hcap : Real.exp (-(J+2*δ)*(N:ℝ)) ≤ (gibbsLaw N β H).real (cap x q₂))
    (hcollar : (gibbsLaw N β H).real (collar x q₁ q₂) ≤
      Real.exp (-(J+G-2*δ)*(N:ℝ))) :
    (gibbsLaw N β H).real (collar x q₁ q₂)/
      denominator β H (sourceProfile J δ q₁ q₂) x ≤
        Real.exp (-(G-4*δ)*(N:ℝ)) := by
  have hh := sourceProfile_contDiff J δ q₁ q₂
  have hhigh : ∀ r ∈ Icc q₂ 1, sourceProfile J δ q₁ q₂ r = 0 :=
    fun r hr => profile_high _ hq hr.1
  have hd := hcap.trans (denominator_cap_lower hN β hH hh q₂ hhigh x hx)
  have hp := denominator_pos hN β hH hh x
  calc
    _ ≤ Real.exp (-(J+G-2*δ)*(N:ℝ))/denominator β H (sourceProfile J δ q₁ q₂) x :=
      div_le_div_of_nonneg_right hcollar hp.le
    _ ≤ Real.exp (-(J+G-2*δ)*(N:ℝ))/Real.exp (-(J+2*δ)*(N:ℝ)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hd
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- The constructed observable satisfies the exact source finite-volume
energy estimate, derived from cap/collar masses and the true derivative. -/
theorem sourceObservable_energy_le (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (J G δ q₁ q₂ a M : ℝ) (hK : 0 ≤ sourceK J δ)
    (hq₁ : -1 < q₁) (hq : q₁ < q₂) (hM : 0 ≤ M)
    (hd : ∀ r ∈ Icc (-1:ℝ) 1, |deriv (sourceProfile J δ q₁ q₂) r| ≤ M)
    (S : Set (Vector N)) (hS : MeasurableSet S)
    (hbad : (gibbsLaw N β H).real Sᶜ ≤ Real.exp (-a*(N:ℝ)))
    (hcap : ∀ x ∈ S, OnSphere x → Real.exp (-(J+2*δ)*(N:ℝ)) ≤
      (gibbsLaw N β H).real (cap x q₂))
    (hcollar : ∀ x ∈ S, OnSphere x → (gibbsLaw N β H).real (collar x q₁ q₂) ≤
      Real.exp (-(J+G-2*δ)*(N:ℝ))) :
    vectorDirichletEnergy β H (sourceObservable β H J δ q₁ q₂) ≤
      4*(N:ℝ)*M^2*(Real.exp (-(G-4*δ)*(N:ℝ))+Real.exp (-a*(N:ℝ))) := by
  have he := barycenter_energy_le_of_collar_ratio hN β hH
    (sourceProfile_contDiff J δ q₁ q₂) (sourceK J δ) q₁ q₂ M
    (Real.exp (-(G-4*δ)*(N:ℝ))) hq₁ hM (Real.exp_pos _).le
    (fun r _ => profile_nonneg _ _ _ hK r) hd
    (fun r hr => profile_low _ hq hr.2) (fun r hr => profile_high _ hq hr.1)
    S hS (fun x hx hxS => source_collar_ratio_le hN β hH J G δ q₁ q₂ hq x hxS
      (hcap x hx hxS) (hcollar x hx hxS))
  exact he.trans (mul_le_mul_of_nonneg_left (add_le_add_right hbad _) (by positivity))

/-- The actual source choice `2K-J-2δ=1` gives the exact error `e⁻ᴺ`.
This statement precedes every asymptotic simplification of the alignment. -/
theorem sourceObservable_alignment_lower (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) (J δ q₁ q₂ : ℝ) (hq₁ : -1 < q₁) (hq : q₁ < q₂)
    (x : Vector N) (hx : OnSphere x)
    (hcap : Real.exp (-(J+2*δ)*(N:ℝ)) ≤ (gibbsLaw N β H).real (cap x q₂)) :
    q₁-(1+q₁)*Real.exp (-(N:ℝ)) ≤
      inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x) := by
  have hh := sourceProfile_contDiff J δ q₁ q₂
  have hhigh : ∀ r ∈ Icc q₂ 1, sourceProfile J δ q₁ q₂ r = 0 :=
    fun r hr => profile_high _ hq hr.1
  have hd := hcap.trans (denominator_cap_lower hN β hH hh q₂ hhigh x hx)
  have he := barycenter_alignment_lower hN β hH hh (sourceK J δ) q₁ hq₁
    (fun r hr => profile_low _ hq hr.2) x hx
  have hr : (1+q₁)*Real.exp (-2*sourceK J δ*(N:ℝ))/
      denominator β H (sourceProfile J δ q₁ q₂) x ≤ (1+q₁)*Real.exp (-(N:ℝ)) := by
    have hi := div_le_div_of_nonneg_left
      (mul_nonneg (by linarith : (0:ℝ) ≤ 1+q₁) (Real.exp_pos (-2*sourceK J δ*(N:ℝ))).le)
      (Real.exp_pos (-(J+2*δ)*(N:ℝ))) hd
    have heq : (1+q₁)*Real.exp (-2*sourceK J δ*(N:ℝ))/Real.exp (-(J+2*δ)*(N:ℝ)) =
        (1+q₁)*Real.exp (-(N:ℝ)) := by
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      unfold sourceK
      ring
    exact hi.trans_eq heq
  change q₁-(1+q₁)*Real.exp (-2*sourceK J δ*(N:ℝ))/
    denominator β H (sourceProfile J δ q₁ q₂) x ≤
      inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x) at he
  linarith

/-- The exact pointwise alignment integrates with only the true exceptional
Gibbs mass. In particular the references outside the good set are retained. -/
theorem sourceObservable_mean_alignment_lower (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (J δ q₁ q₂ a : ℝ)
    (hq₁ : -1 < q₁) (hq : q₁ < q₂) (S : Set (Vector N)) (hS : MeasurableSet S)
    (hbad : (gibbsLaw N β H).real Sᶜ ≤ Real.exp (-a*(N:ℝ)))
    (hcap : ∀ x ∈ S, OnSphere x → Real.exp (-(J+2*δ)*(N:ℝ)) ≤
      (gibbsLaw N β H).real (cap x q₂)) :
    q₁-(1+q₁)*(Real.exp (-(N:ℝ))+Real.exp (-a*(N:ℝ))) ≤
      ∫ x, inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x) ∂gibbsLaw N β H := by
  let := gibbsLaw_probability hN β hH
  let A : ℝ := q₁-(1+q₁)*Real.exp (-(N:ℝ))
  have hp : Continuous (fun x => inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x)) :=
    spin_contDiff.continuous.inner (sourceObservable_contDiff hN β hH J δ q₁ q₂).continuous
  have hiBad : Integrable (Sᶜ.indicator (fun _ => (1+q₁))) (gibbsLaw N β H) :=
    (integrable_const _).indicator hS.compl
  have hpoint : ∀ᵐ x ∂gibbsLaw N β H, A-Sᶜ.indicator (fun _ => (1+q₁)) x ≤
      inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x) := by
    filter_upwards [gibbsLaw_support hN β H] with x hx
    have hxS := (onSphere_iff_norm_sq x).mpr hx
    by_cases hxG : x ∈ S
    · rw [Set.indicator_of_notMem (show x ∉ Sᶜ from by simpa), sub_zero]
      exact sourceObservable_alignment_lower hN β hH J δ q₁ q₂ hq₁ hq x hxS (hcap x hxG hxS)
    · rw [Set.indicator_of_mem (show x ∈ Sᶜ from hxG)]
      have hh := abs_real_inner_le_norm (spin x) (sourceObservable β H J δ q₁ q₂ x)
      rw [spin_norm hN x hxS, one_mul] at hh
      have hb := sourceObservable_norm_le_one hN β hH J δ q₁ q₂ x
      have hlow : -1 ≤ inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x) :=
        (abs_le.mp (hh.trans hb)).1
      dsimp [A]
      nlinarith [Real.exp_pos (-(N:ℝ))]
  have hi := integral_mono_ae ((integrable_const A).sub hiBad)
    (integrable_gibbs_of_continuous hN β hH hp) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const A) hiBad, integral_indicator hS.compl,
    setIntegral_const] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hm := mul_le_mul_of_nonneg_right hbad (show (0:ℝ) ≤ 1+q₁ by linarith)
  dsimp [A] at hi
  nlinarith

/-- Both source alignment thresholds are uniform in the field and good set. -/
theorem source_alignment_errors_eventually {q₁ q₀ : ℝ} (hq₁ : 0 < q₁) (hq₀ : q₀ < q₁) :
    ∀ᶠ N : ℕ in atTop, (1+q₁)*Real.exp (-(N:ℝ)) ≤ min (q₁-q₀) (q₁/4) := by
  have ht : Tendsto (fun N : ℕ => (1+q₁)*Real.exp (-(N:ℝ))) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul (1+q₁)
  have hm : (0:ℝ) < min (q₁-q₀) (q₁/4) := lt_min (by linarith) (by positivity)
  exact (ht.eventually (gt_mem_nhds hm)).mono (fun _ h => h.le)

/-- The source construction supplies a single fixed smooth profile and
dimension-independent energy constants before every dimension, field and
good set. The only deterministic inputs are the actual source Gibbs masses. -/
theorem sourceObservable_estimates_eventually (J G δ q₁ q₂ a q₀ : ℝ)
    (hJ : 0 < J) (hδ : 0 ≤ δ) (hgap : 4*δ < G) (ha : 0 < a)
    (hq₁ : 0 < q₁) (hq : q₁ < q₂) (hq₀ : q₀ < q₁) :
    ∃ M C c : ℝ, 0 ≤ M ∧ 0 < C ∧ 0 < c ∧
      c=min (G-4*δ) a/2 ∧
      (∀ r ∈ Icc (-1:ℝ) 1, |deriv (sourceProfile J δ q₁ q₂) r| ≤ M) ∧
      ∀ᶠ N : ℕ in atTop, ∀ (β : ℝ) (H : Vector N → ℝ), Continuous H →
        ∀ S : Set (Vector N), MeasurableSet S →
        (gibbsLaw N β H).real Sᶜ ≤ Real.exp (-a*(N:ℝ)) →
        (∀ x ∈ S, OnSphere x → Real.exp (-(J+2*δ)*(N:ℝ)) ≤
          (gibbsLaw N β H).real (cap x q₂)) →
        (∀ x ∈ S, OnSphere x → (gibbsLaw N β H).real (collar x q₁ q₂) ≤
          Real.exp (-(J+G-2*δ)*(N:ℝ))) →
        ContDiff ℝ ∞ (sourceObservable β H J δ q₁ q₂) ∧
        (∀ x, ‖sourceObservable β H J δ q₁ q₂ x‖ ≤ 1) ∧
        vectorDirichletEnergy β H (sourceObservable β H J δ q₁ q₂) ≤ C*Real.exp (-c*(N:ℝ)) ∧
        (∀ x ∈ S, OnSphere x → q₀ ≤ inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x) ∧
          3*q₁/4 ≤ inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x)) ∧
        q₁-(1+q₁)*(Real.exp (-(N:ℝ))+Real.exp (-a*(N:ℝ))) ≤
          ∫ x, inner ℝ (spin x) (sourceObservable β H J δ q₁ q₂ x) ∂gibbsLaw N β H := by
  obtain ⟨M,hM,hd⟩ := exists_profile_deriv_bound (sourceK J δ) q₁ q₂
  have hg : 0 < G-4*δ := by linarith
  have hc : 0 < min (G-4*δ) a/2 := by positivity
  refine ⟨M,8*(M^2+1),min (G-4*δ) a/2,hM,by positivity,hc,rfl,hd,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),
    SlowEquilibration.dimension_times_two_exponentials_eventually hg ha M,
    source_alignment_errors_eventually hq₁ hq₀] with N hN hE hsmall
  intro β H hH S hS hbad hcap hcollar
  have hK : 0 ≤ sourceK J δ := by unfold sourceK; linarith
  have hq₁' : -1 < q₁ := by linarith
  refine ⟨sourceObservable_contDiff hN β hH J δ q₁ q₂,
    sourceObservable_norm_le_one hN β hH J δ q₁ q₂,
    (sourceObservable_energy_le hN β hH J G δ q₁ q₂ a M hK hq₁' hq hM hd
      S hS hbad hcap hcollar).trans hE,?_,
    sourceObservable_mean_alignment_lower hN β hH J δ q₁ q₂ a hq₁' hq S hS hbad hcap⟩
  intro x hx hxS
  have he := sourceObservable_alignment_lower hN β hH J δ q₁ q₂ hq₁' hq x hxS (hcap x hx hxS)
  have h1 := hsmall.trans (min_le_left (q₁-q₀) (q₁/4))
  have h2 := hsmall.trans (min_le_right (q₁-q₀) (q₁/4))
  constructor <;> linarith

end
end SlowEquilibration.SphericalBarycenter
