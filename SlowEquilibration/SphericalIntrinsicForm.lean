-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalIntrinsicExtension
public import SlowEquilibration.SphericalEnergy

/-! Actual Gibbs measures and actual Dirichlet pairings for intrinsically
defined sphere functions, with proved independence of ambient representatives. -/
@[expose] public section
namespace SlowEquilibration.SphericalIntrinsicExtension
open MeasureTheory Set Filter
open SphericalModel SphericalForm
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluate the actual intrinsic function on the sphere. Its values away
from the sphere do not affect any of the measures below. -/
def sphereValue (n : ℕ) (f : RoundSphere n → ℝ) (x : Vector (n+1)) : ℝ :=
  if hx : ‖x‖^2=(n+1 : ℕ) then f ⟨x,hx⟩ else 0

lemma sphereValue_restrict (n : ℕ) (f : RoundSphere n → ℝ) (x : RoundSphere n) :
    sphereValue n f (x : Vector (n+1))=f x := by
  simp only [sphereValue,dite_eq_left x.property]

/-- The true intrinsic Gibbs law, defined directly by intrinsic values and
the literal normalized round-sphere measure. -/
def intrinsicGibbsLaw (n : ℕ) (β : ℝ) (H : RoundSphere n → ℝ) : Measure (Vector (n+1)) :=
  gibbsLaw (n+1) β (sphereValue n H)

lemma partition_eq_of_agree_on_sphere {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H G : Vector N → ℝ) (he : ∀ x, ‖x‖^2=(N:ℝ) → H x=G x) :
    partition N β H=partition N β G := by
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  rw [he x hx]

lemma gibbsLaw_eq_of_agree_on_sphere {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H G : Vector N → ℝ) (he : ∀ x, ‖x‖^2=(N:ℝ) → H x=G x) :
    gibbsLaw N β H=gibbsLaw N β G := by
  have hz := partition_eq_of_agree_on_sphere hN β H G he
  apply withDensity_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  simp only [gibbsDensity,hz,he x hx]

theorem intrinsicGibbsLaw_eq_of_extension (n : ℕ) (β : ℝ) (H : RoundSphere n → ℝ)
    (F : Vector (n+1) → ℝ) (he : ∀ x : RoundSphere n, F x=H x) :
    intrinsicGibbsLaw n β H=gibbsLaw (n+1) β F := by
  apply gibbsLaw_eq_of_agree_on_sphere (by omega)
  intro x hx
  exact (sphereValue_restrict n H ⟨x,hx⟩).trans (he ⟨x,hx⟩).symm

theorem intrinsicGibbsLaw_eq_ambientExtension (n : ℕ) (β : ℝ) (H : RoundSphere n → ℝ) :
    intrinsicGibbsLaw n β H=gibbsLaw (n+1) β (ambientExtension n H) :=
  intrinsicGibbsLaw_eq_of_extension n β H _ (ambientExtension_restrict n H)

theorem intrinsicGibbsLaw_probability (n : ℕ) (β : ℝ) {m : ℕ∞} (H : RoundSphere n → ℝ)
    (hH : IntrinsicContDiff n m H) : IsProbabilityMeasure (intrinsicGibbsLaw n β H) := by
  rw [intrinsicGibbsLaw_eq_ambientExtension]
  exact gibbsLaw_probability (by omega) β (ambientExtension_contDiff n m H hH).continuous

/-- A canonical representation of the intrinsic gradient. Its agreement
with every differentiable representative is proved below. -/
def intrinsicGradient (n : ℕ) (f : RoundSphere n → ℝ) (x : RoundSphere n) : Vector (n+1) :=
  surfaceGradient (ambientExtension n f) x

theorem intrinsicGradient_eq_of_extension (n : ℕ) (f : RoundSphere n → ℝ)
    (hf : IntrinsicContDiff n 1 f) (F : Vector (n+1) → ℝ) (hF : ContDiff ℝ 1 F)
    (he : ∀ x : RoundSphere n, F x=f x) (x : RoundSphere n) :
    intrinsicGradient n f x=surfaceGradient F x := by
  apply surfaceGradient_eq_of_agree_on_sphere (by omega) _ _ _
    ((onSphere_iff_norm_sq _).mpr x.property)
    ((ambientExtension_contDiff n 1 f hf).differentiable (by norm_num) _)
    (hF.differentiable (by norm_num) _)
  intro y hy
  have hy' := (onSphere_iff_norm_sq y).mp hy
  exact (ambientExtension_restrict n f ⟨y,hy'⟩).trans (he ⟨y,hy'⟩).symm

/-- The actual intrinsic Dirichlet pairing, integrated against the actual
intrinsic Gibbs measure. -/
def intrinsicDirichletForm (n : ℕ) (β : ℝ) (H f g : RoundSphere n → ℝ) : ℝ :=
  ∫ x, if hx : ‖x‖^2=(n+1 : ℕ) then
    inner ℝ (intrinsicGradient n f ⟨x,hx⟩) (intrinsicGradient n g ⟨x,hx⟩) else 0
    ∂intrinsicGibbsLaw n β H

/-- Every choice of actual C¹ ambient representatives gives the same
intrinsic Gibbs-weighted Dirichlet form. -/
theorem intrinsicDirichletForm_eq_of_extensions (n : ℕ) (β : ℝ)
    (H f g : RoundSphere n → ℝ) (hf : IntrinsicContDiff n 1 f) (hg : IntrinsicContDiff n 1 g)
    (V F G : Vector (n+1) → ℝ) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hVeq : ∀ x : RoundSphere n, V x=H x)
    (hFeq : ∀ x : RoundSphere n, F x=f x) (hGeq : ∀ x : RoundSphere n, G x=g x) :
    intrinsicDirichletForm n β H f g=dirichletForm (n+1) β V F G := by
  unfold intrinsicDirichletForm dirichletForm
  rw [intrinsicGibbsLaw_eq_of_extension n β H V hVeq]
  apply integral_congr_ae
  filter_upwards [gibbsLaw_support (show 1 ≤ n+1 by omega) β V] with x hx
  rw [dite_eq_left hx,intrinsicGradient_eq_of_extension n f hf F hF hFeq,
    intrinsicGradient_eq_of_extension n g hg G hG hGeq]

theorem intrinsicDirichletForm_eq_ambientExtensions (n : ℕ) (β : ℝ)
    (H f g : RoundSphere n → ℝ) (hf : IntrinsicContDiff n 1 f) (hg : IntrinsicContDiff n 1 g) :
    intrinsicDirichletForm n β H f g=
      dirichletForm (n+1) β (ambientExtension n H) (ambientExtension n f) (ambientExtension n g) :=
  intrinsicDirichletForm_eq_of_extensions n β H f g hf hg _ _ _
    (ambientExtension_contDiff n 1 f hf) (ambientExtension_contDiff n 1 g hg)
    (ambientExtension_restrict n H) (ambientExtension_restrict n f) (ambientExtension_restrict n g)

end
end SlowEquilibration.SphericalIntrinsicExtension
