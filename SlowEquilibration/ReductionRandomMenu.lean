-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionMenuAllTime

/-! Independent random finite menus, with independence represented by the
literal product law of menu randomness and disorder. Conditioning and
integration are proved using actual kernels and Fubini. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionFiniteMenu
open MeasureTheory ProbabilityTheory Set Filter
open ReductionJointInformation ReductionEndpointTransfer VaryingProbability
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι R Ω X : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace R] [MeasurableSpace Ω] [MeasurableSpace X]

def randomInitial (ν : R → ι → Measure X) (hν : ∀ j, Measurable (fun r => ν r j))
    (j : ι) : Kernel (R × Ω) X where
  toFun z := ν z.1 j
  measurable' := (hν j).comp measurable_fst

instance randomInitial_isMarkov (ν : R → ι → Measure X)
    (hν : ∀ j, Measurable (fun r => ν r j)) [∀ r j, IsProbabilityMeasure (ν r j)] (j : ι) :
    IsMarkovKernel (randomInitial (Ω := Ω) ν hν j) where
  isProbabilityMeasure z := by
    change IsProbabilityMeasure (ν z.1 j)
    infer_instance

def liftTransition (R : Type*) [MeasurableSpace R] (K : Kernel (Ω × X) X) :
    Kernel ((R × Ω) × X) X :=
  K.comap (fun z => (z.1.2,z.2)) ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

instance liftTransition_isMarkov (K : Kernel (Ω × X) X) [IsMarkovKernel K] :
    IsMarkovKernel (liftTransition R K) := by unfold liftTransition; infer_instance

def liftBand (R : Type*) (B : Set (Ω × X)) : Set ((R × Ω) × X) :=
  (fun z => (z.1.2,z.2)) ⁻¹' B

lemma liftBand_measurable {B : Set (Ω × X)} (hB : MeasurableSet B) :
    MeasurableSet (liftBand R B) :=
  hB.preimage ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

lemma liftTransition_conditional (K : Kernel (Ω × X) X) (r : R) (ω : Ω) :
    conditionalKernel (liftTransition R K) (r,ω)=conditionalKernel K ω := by
  ext x A hA
  rfl

lemma random_conditionalMass (ν : R → ι → Measure X)
    (hν : ∀ j, Measurable (fun r => ν r j)) [∀ r j, IsProbabilityMeasure (ν r j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K] (B : Set (Ω × X)) (r : R) (ω : Ω) (j : ι) :
    conditionalMass (randomInitial ν hν j) (liftTransition R K) (liftBand R B) (r,ω) =
      conditionalMass (Kernel.const Ω (ν r j)) K B ω := by
  unfold conditionalMass
  rw [evolvedKernel_apply,evolvedKernel_apply,liftTransition_conditional]
  rfl

/-- Integrating the conditional menu bound proves the same Kq bound under
the true independent joint law, uniformly over every menu realization. -/
theorem random_menuError_integral_eq (ρ : Measure R) [IsProbabilityMeasure ρ]
    (d : Measure Ω) [IsProbabilityMeasure d]
    (ν : R → ι → Measure X) (hν : ∀ j, Measurable (fun r => ν r j))
    [∀ r j, IsProbabilityMeasure (ν r j)]
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    {B : Set (Ω × X)} (hB : MeasurableSet B) {q : ℝ}
    (hequal : ∀ x : X, (∫ ω, (K (ω,x)).real (Prod.mk ω ⁻¹' B) ∂d)=q) :
    (∫ z, menuError (randomInitial ν hν) (liftTransition R K) (liftBand R B) z ∂ρ.prod d) =
      (Fintype.card ι)*q := by
  rw [integral_prod _ (menuError_integrable (ρ.prod d) _ _ (liftBand_measurable hB))]
  have hi (r : R) :
      (∫ ω, menuError (randomInitial ν hν) (liftTransition R K) (liftBand R B) (r,ω) ∂d) =
        (Fintype.card ι)*q := by
    simp_rw [menuError,random_conditionalMass]
    exact prescribed_menuError_integral_eq d (ν r) K hB hequal
  simp_rw [hi]
  rw [integral_const,probReal_univ,one_smul]

section Varying
variable {Rₙ Ωₙ Xₙ ιₙ : ℕ → Type*}
  [∀ N, MeasurableSpace (Rₙ N)] [∀ N, MeasurableSpace (Ωₙ N)]
  [∀ N, MeasurableSpace (Xₙ N)] [∀ N, Fintype (ιₙ N)] [∀ N, Nonempty (ιₙ N)]

/-- Source independent-random-menu conclusion in the literal joint
probability, uniformly over all field- and menu-selected weights. -/
theorem independent_random_menu_endpoint_separation
    (ρ : ∀ N, Measure (Rₙ N)) [∀ N, IsProbabilityMeasure (ρ N)]
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (ν : ∀ N, Rₙ N → ιₙ N → Measure (Xₙ N))
    (hν : ∀ N j, Measurable (fun r => ν N r j)) [∀ N r j, IsProbabilityMeasure (ν N r j)]
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ωₙ N × Xₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (K N)]
    (B : ∀ N, ℝ → Set (Ωₙ N × Xₙ N)) (hB : ∀ N M, MeasurableSet (B N M))
    (q : ℕ → ℝ → ℝ)
    (hequal : ∀ N M x, (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N M) ∂d N)=q N M)
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (hsize : ∀ M : ℝ, 0 < M → Tendsto (fun N => (Fintype.card (ιₙ N):ℝ)*q N M) atTop (𝓝 0)) :
    InProbability (fun N => (ρ N).prod (d N))
      (fun N z => menuDistance (fun j => conditionalKernel (K N) z.2 ∘ₘ ν N z.1 j) (π N z.2)) 1 := by
  have h := menu_endpoint_separation_of_capture (fun N => (ρ N).prod (d N))
    (fun N => randomInitial (Ω := Ωₙ N) (ν N) (hν N))
    (fun N => (π N).comap Prod.snd measurable_snd)
    (fun N => liftTransition (Rₙ N) (K N))
    (fun N M => liftBand (Rₙ N) (B N M)) (fun N M => liftBand_measurable (hB N M))
    ?_ ?_
  · convert h using 1
    funext N z
    congr 1
    funext j
    rw [evolvedKernel_apply,liftTransition_conditional]
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
    simpa only [random_menuError_integral_eq _ _ _ _ _ (hB _ _) (hequal _ _)] using hsize M hM

end Varying
end SlowEquilibration.ReductionFiniteMenu
