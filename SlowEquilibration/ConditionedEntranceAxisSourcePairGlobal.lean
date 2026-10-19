-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisSignedEnergyGlobal

/-! Exact global averaging of a source-pairing identity under the
physical axis-dependent Gibbs tilt. The fibre partition ratio is retained
in the disintegration and disappears only after the four terms combine. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem axisGibbs_source_pair_global
    {N : ℕ} (hN : 1≤N) (β : ℝ)
    (H₀ : Vector N→ℝ) (hH₀ : Continuous H₀)
    (H : Vector N→Vector N→ℝ)
    (hH : Continuous (fun z : Vector N×Vector N => H z.1 z.2))
    (fI fR fD fC : Vector N×Vector N→ℝ) (θ : ℝ)
    (hM : 0 < ∫ z : Vector N×Vector N,
      Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))
    (hIi : Integrable fI (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hRi : Integrable fR (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hDi : Integrable fD (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hCi : Integrable fC (normalizedTilt
      ((sphereLaw N).prod (gibbsLaw N β H₀))
      (fun z => β*(H z.1 z.2-H₀ z.2))
      (∫ z, Real.exp (β*(H z.1 z.2-H₀ z.2))
        ∂((sphereLaw N).prod (gibbsLaw N β H₀)))))
    (hpoint : ∀ u : Vector N, OnSphere u →
      θ*(∫ x, fI (u,x) ∂gibbsLaw N β (H u))=
        (∫ x, fR (u,x) ∂gibbsLaw N β (H u))+
        θ*(∫ x, fD (u,x) ∂gibbsLaw N β (H u))-
        (∫ x, fC (u,x) ∂gibbsLaw N β (H u))) :
    let w : Vector N×Vector N→ℝ := fun z => β*(H z.1 z.2-H₀ z.2)
    let M := ∫ z, Real.exp (w z)
      ∂((sphereLaw N).prod (gibbsLaw N β H₀))
    let ν := normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H₀)) w M
    θ*(∫ z, fI z ∂ν)=
      (∫ z, fR z ∂ν)+θ*(∫ z, fD z ∂ν)-
      (∫ z, fC z ∂ν) := by
  dsimp only
  let m : Vector N→ℝ := fun u => partition N β (H u)/partition N β H₀
  let M := ∫ z : Vector N×Vector N,
    Real.exp (β*(H z.1 z.2-H₀ z.2))
      ∂((sphereLaw N).prod (gibbsLaw N β H₀))
  let t : Vector N→ℝ := fun u => m u/M
  let I : Vector N→ℝ := fun u => ∫ x, fI (u,x) ∂gibbsLaw N β (H u)
  let R : Vector N→ℝ := fun u => ∫ x, fR (u,x) ∂gibbsLaw N β (H u)
  let D : Vector N→ℝ := fun u => ∫ x, fD (u,x) ∂gibbsLaw N β (H u)
  let C : Vector N→ℝ := fun u => ∫ x, fC (u,x) ∂gibbsLaw N β (H u)
  obtain ⟨hIint,hIeq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fI hM hIi
  obtain ⟨hRint,hReq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fR hM hRi
  obtain ⟨hDint,hDeq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fD hM hDi
  obtain ⟨hCint,hCeq⟩ := axisGibbs_globalTilt_integral_disintegration_L1
    hN β H₀ hH₀ H hH fC hM hCi
  have hp : ∀ᵐ u ∂sphereLaw N,
      θ*I u=R u+θ*D u-C u := by
    filter_upwards [sphereLaw_support hN] with u hu
    exact hpoint u ((onSphere_iff_norm_sq u).mpr hu)
  have heq : (∫ u, θ*(t u*I u) ∂sphereLaw N)=
      ∫ u, (t u*R u+θ*(t u*D u))-t u*C u ∂sphereLaw N := by
    apply integral_congr_ae
    exact hp.mono (fun u hu => by
      change θ*(t u*I u)=(t u*R u+θ*(t u*D u))-t u*C u
      calc
        θ*(t u*I u)=t u*(θ*I u) := by ring
        _=t u*(R u+θ*D u-C u) := by rw [hu]
        _=_ := by ring)
  have heq' : θ*(∫ u,t u*I u ∂sphereLaw N)=
      (∫ u,t u*R u ∂sphereLaw N)+
      θ*(∫ u,t u*D u ∂sphereLaw N)-
      (∫ u,t u*C u ∂sphereLaw N) := by
    have hRD : Integrable (fun u => t u*R u+θ*(t u*D u))
        (sphereLaw N) := hRint.add (hDint.const_mul θ)
    have hrw := integral_sub hRD hCint
    rw [integral_add hRint (hDint.const_mul θ)] at hrw
    simpa only [integral_const_mul] using heq.trans hrw
  rw [hIeq,hReq,hDeq,hCeq] at heq'
  exact heq'

end SlowEquilibration.ConditionedEntrance
