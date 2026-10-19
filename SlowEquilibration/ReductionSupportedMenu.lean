-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionRandomMenu
public import SlowEquilibration.ReductionInformationSupport

/-! Full source menu selection with actual spherical support. Equal
averaged entry mass is required only on the support of the prescribed
initial measures, and independent menus use their literal product law. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionFiniteMenu
open MeasureTheory ProbabilityTheory Set Filter
open ReductionJointInformation ReductionEndpointTransfer ReductionInformationSupport VaryingProbability
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι R Ω X : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace R] [MeasurableSpace Ω] [MeasurableSpace X]

theorem prescribed_mass_integral_eq_ae (d : Measure Ω) [IsProbabilityMeasure d]
    (ν : Measure X) [IsProbabilityMeasure ν] (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) {q : ℝ}
    (hequal : ∀ᵐ x ∂ν, (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d)=q) :
    (∫ ω, conditionalMass (Kernel.const Ω ν) K B ω ∂d)=q := by
  have hc : (Kernel.const Ω ν) ∘ₘ d=ν := by
    change d.bind (fun _ => ν)=ν
    rw [Measure.bind_const,measure_univ,one_smul]
  have he : ∀ᵐ x ∂((Kernel.const Ω ν) ∘ₘ d),
      (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d)=q := by rwa [hc]
  have h := reference_mass_eq_of_ae_equal_mass d (Kernel.const Ω ν) K hB he
  rw [hc] at h
  have hi := retained_joint_mass_eq_integral d (Kernel.const Ω ν) K hB
  rw [Measure.compProd_const] at hi
  exact hi.symm.trans h

theorem prescribed_menuError_integral_eq_ae (d : Measure Ω) [IsProbabilityMeasure d]
    (ν : ι → Measure X) [∀ j, IsProbabilityMeasure (ν j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) {q : ℝ}
    (hequal : ∀ j, ∀ᵐ x ∂ν j, (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d)=q) :
    (∫ ω, menuError (fun j => Kernel.const Ω (ν j)) K B ω ∂d) = (Fintype.card ι)*q := by
  rw [menuError_integral_eq_sum d _ K hB]
  simp_rw [prescribed_mass_integral_eq_ae d _ K hB (hequal _)]
  simp

theorem random_menuError_integral_eq_ae (ρ : Measure R) [IsProbabilityMeasure ρ]
    (d : Measure Ω) [IsProbabilityMeasure d]
    (ν : R → ι → Measure X) (hν : ∀ j, Measurable (fun r => ν r j))
    [∀ r j, IsProbabilityMeasure (ν r j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) {q : ℝ}
    (hequal : ∀ r j, ∀ᵐ x ∂ν r j, (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d)=q) :
    (∫ z, menuError (randomInitial ν hν) (liftTransition R K) (liftBand R B) z ∂ρ.prod d) =
      (Fintype.card ι)*q := by
  rw [integral_prod _ (menuError_integrable (ρ.prod d) _ _ (liftBand_measurable hB))]
  have hi (r : R) :
      (∫ ω, menuError (randomInitial ν hν) (liftTransition R K) (liftBand R B) (r,ω) ∂d) =
        (Fintype.card ι)*q := by
    simp_rw [menuError,random_conditionalMass]
    exact prescribed_menuError_integral_eq_ae d (ν r) K hB (hequal r)
  simp_rw [hi]
  rw [integral_const,probReal_univ,one_smul]

section Varying
variable {Rₙ Ωₙ Xₙ ιₙ : ℕ → Type*}
  [∀ N, MeasurableSpace (Rₙ N)] [∀ N, MeasurableSpace (Ωₙ N)]
  [∀ N, MeasurableSpace (Xₙ N)] [∀ N, Fintype (ιₙ N)] [∀ N, Nonempty (ιₙ N)]

/-- Source cor:red-selection for prescribed sphere-supported laws,
uniformly over every convex weight and every time up to T_N. -/
theorem supported_menu_allTime_separation
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (ν : ∀ N, ιₙ N → Measure (Xₙ N)) [∀ N j, IsProbabilityMeasure (ν N j)]
    (S : ∀ N, Set (Xₙ N)) (hsupport : ∀ N j, ∀ᵐ x ∂ν N j, x ∈ S N)
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ωₙ N × Xₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (K N)]
    (P : ∀ N, Ωₙ N → ℝ≥0 → Kernel (Xₙ N) (Xₙ N)) [∀ N ω t, IsMarkovKernel (P N ω t)]
    (hcomp : ∀ N ω s t, P N ω (s+t)=P N ω s ∘ₖ P N ω t)
    (hinv : ∀ N ω t, P N ω t ∘ₘ π N ω=π N ω)
    (T : ℕ → ℝ≥0) (hK : ∀ N ω, conditionalKernel (K N) ω=P N ω (T N))
    (B : ∀ N, ℝ → Set (Ωₙ N × Xₙ N)) (hB : ∀ N M, MeasurableSet (B N M))
    (q : ℕ → ℝ → ℝ)
    (hequal : ∀ N M, 0 < M → ∀ x ∈ S N,
      (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N M) ∂d N)=q N M)
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (hsize : ∀ M : ℝ, 0 < M → Tendsto (fun N => (Fintype.card (ιₙ N):ℝ)*q N M) atTop (𝓝 0)) :
    InProbability d (fun N ω => menuAllTimeDistance (P N ω) (ν N) (π N ω) (T N)) 1 := by
  have herror (M : ℝ) (hM : 0 < M) :
      Tendsto (fun N => ∫ ω, menuError (fun j => Kernel.const (Ωₙ N) (ν N j))
        (K N) (B N M) ω ∂d N) atTop (𝓝 0) := by
    have he (N : ℕ) := prescribed_menuError_integral_eq_ae (d N) (ν N) (K N) (hB N M)
      (fun j => (hsupport N j).mono (fun x hx => hequal N M hM x hx))
    simpa only [he] using hsize M hM
  have h := menu_endpoint_separation_of_capture d (fun N j => Kernel.const (Ωₙ N) (ν N j))
    π K B hB hcapture herror
  convert h using 1
  funext N ω
  rw [menuAllTimeDistance_eq_endpoint _ _ _ (hcomp N ω) (hinv N ω)]
  congr 1
  funext j
  rw [evolvedKernel_apply,hK]
  rfl

/-- The complete independent-random-menu variant, under the literal
product of menu randomness and disorder, with the original sphere support. -/
theorem supported_random_menu_allTime_separation
    (ρ : ∀ N, Measure (Rₙ N)) [∀ N, IsProbabilityMeasure (ρ N)]
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (ν : ∀ N, Rₙ N → ιₙ N → Measure (Xₙ N))
    (hν : ∀ N j, Measurable (fun r => ν N r j)) [∀ N r j, IsProbabilityMeasure (ν N r j)]
    (S : ∀ N, Set (Xₙ N)) (hsupport : ∀ N r j, ∀ᵐ x ∂ν N r j, x ∈ S N)
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ωₙ N × Xₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (K N)]
    (P : ∀ N, Ωₙ N → ℝ≥0 → Kernel (Xₙ N) (Xₙ N)) [∀ N ω t, IsMarkovKernel (P N ω t)]
    (hcomp : ∀ N ω s t, P N ω (s+t)=P N ω s ∘ₖ P N ω t)
    (hinv : ∀ N ω t, P N ω t ∘ₘ π N ω=π N ω)
    (T : ℕ → ℝ≥0) (hK : ∀ N ω, conditionalKernel (K N) ω=P N ω (T N))
    (B : ∀ N, ℝ → Set (Ωₙ N × Xₙ N)) (hB : ∀ N M, MeasurableSet (B N M))
    (q : ℕ → ℝ → ℝ)
    (hequal : ∀ N M, 0 < M → ∀ x ∈ S N,
      (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N M) ∂d N)=q N M)
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (hsize : ∀ M : ℝ, 0 < M → Tendsto (fun N => (Fintype.card (ιₙ N):ℝ)*q N M) atTop (𝓝 0)) :
    InProbability (fun N => (ρ N).prod (d N))
      (fun N z => menuAllTimeDistance (P N z.2) (ν N z.1) (π N z.2) (T N)) 1 := by
  have h := menu_endpoint_separation_of_capture (fun N => (ρ N).prod (d N))
    (fun N => randomInitial (Ω := Ωₙ N) (ν N) (hν N))
    (fun N => (π N).comap Prod.snd measurable_snd)
    (fun N => liftTransition (Rₙ N) (K N))
    (fun N M => liftBand (Rₙ N) (B N M)) (fun N M => liftBand_measurable (hB N M)) ?_ ?_
  · convert h using 1
    funext N z
    rw [menuAllTimeDistance_eq_endpoint _ _ _ (hcomp N z.2) (hinv N z.2)]
    congr 1
    funext j
    rw [evolvedKernel_apply,liftTransition_conditional,hK]
    rfl
  · intro η hη
    obtain ⟨M,hM,hcap⟩ := hcapture η hη
    refine ⟨M,hM,?_⟩
    filter_upwards [hcap] with N hN
    change (∫ z, (π N z.2).real (Prod.mk z.2 ⁻¹' B N M)ᶜ ∂(ρ N).prod (d N)) < η
    rw [integral_fun_snd (μ := ρ N) (ν := d N)
      (fun ω => (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ),probReal_univ,one_smul]
    exact hN
  · intro M hM
    have he (N : ℕ) := random_menuError_integral_eq_ae (ρ N) (d N) (ν N) (hν N) (K N) (hB N M)
      (fun r j => (hsupport N r j).mono (fun x hx => hequal N M hM x hx))
    simpa only [he] using hsize M hM

end Varying
end SlowEquilibration.ReductionFiniteMenu
