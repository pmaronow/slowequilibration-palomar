-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ReductionMenuTransfer

/-! Uniform finite-menu separation over every source time and every
simplex weight, with actual stationary Markov-semigroup contraction. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ReductionFiniteMenu
open MeasureTheory ProbabilityTheory Set Filter
open ReductionJointInformation ReductionEndpointTransfer VaryingProbability
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι Ω X : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω] [MeasurableSpace X]

/-- Literal nested infimum over all probability weights and all times in
the source closed interval. -/
def menuAllTimeDistance (P : ℝ≥0 → Kernel X X) (ν : ι → Measure X)
    (π : Measure X) (T : ℝ≥0) : ℝ :=
  ⨅ w : Weights ι, allTimeDistance P (mixture ν w) π T

theorem menuAllTimeDistance_eq_endpoint (P : ℝ≥0 → Kernel X X)
    [∀ t, IsMarkovKernel (P t)] (ν : ι → Measure X) [∀ j, IsProbabilityMeasure (ν j)]
    (π : Measure X) [IsProbabilityMeasure π]
    (hcomp : ∀ s t, P (s+t)=P s ∘ₖ P t) (hinv : ∀ t, P t ∘ₘ π=π) (T : ℝ≥0) :
    menuAllTimeDistance P ν π T = menuDistance (fun j => P T ∘ₘ ν j) π := by
  unfold menuAllTimeDistance menuDistance
  simp_rw [allTimeDistance_eq_endpoint P _ π hcomp hinv T,evolve_mixture]

theorem menuAllTimeDistance_measurable [MeasurableSpace.CountablyGenerated X]
    (P : Ω → ℝ≥0 → Kernel X X) [∀ ω t, IsMarkovKernel (P ω t)]
    (ν : ι → Kernel Ω X) [∀ j, IsMarkovKernel (ν j)]
    (π : Kernel Ω X) [IsMarkovKernel π]
    (hcomp : ∀ ω s t, P ω (s+t)=P ω s ∘ₖ P ω t)
    (hinv : ∀ ω t, P ω t ∘ₘ π ω=π ω) (T : ℝ≥0)
    (K : Kernel (Ω × X) X) [IsMarkovKernel K]
    (hK : ∀ ω, conditionalKernel K ω=P ω T) :
    Measurable (fun ω => menuAllTimeDistance (P ω) (fun j => ν j ω) (π ω) T) := by
  have he : (fun ω => menuAllTimeDistance (P ω) (fun j => ν j ω) (π ω) T) =
      (fun ω => menuDistance (fun j => evolvedKernel (ν j) K ω) (π ω)) := by
    funext ω
    rw [menuAllTimeDistance_eq_endpoint _ _ _ (hcomp ω) (hinv ω)]
    congr 1
    funext j
    rw [evolvedKernel_apply,hK]
  rw [he]
  exact menu_endpoint_measurable ν K π

section Varying
variable {Ωₙ Xₙ ιₙ : ℕ → Type*}
  [∀ N, MeasurableSpace (Ωₙ N)] [∀ N, MeasurableSpace (Xₙ N)]
  [∀ N, Fintype (ιₙ N)] [∀ N, Nonempty (ιₙ N)]

/-- Exact source selection over all convex weights and all times. The
semigroup, its stationary law, the capture premise, and the original
K_N q_N,M condition are explicit. -/
theorem prescribed_menu_allTime_separation
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (ν : ∀ N, ιₙ N → Measure (Xₙ N)) [∀ N j, IsProbabilityMeasure (ν N j)]
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ωₙ N × Xₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (K N)]
    (P : ∀ N, Ωₙ N → ℝ≥0 → Kernel (Xₙ N) (Xₙ N)) [∀ N ω t, IsMarkovKernel (P N ω t)]
    (hcomp : ∀ N ω s t, P N ω (s+t)=P N ω s ∘ₖ P N ω t)
    (hinv : ∀ N ω t, P N ω t ∘ₘ π N ω=π N ω)
    (T : ℕ → ℝ≥0) (hK : ∀ N ω, conditionalKernel (K N) ω=P N ω (T N))
    (B : ∀ N, ℝ → Set (Ωₙ N × Xₙ N)) (hB : ∀ N M, MeasurableSet (B N M))
    (q : ℕ → ℝ → ℝ)
    (hequal : ∀ N M x, (∫ ω, (K N (ω,x)).real (Prod.mk ω ⁻¹' B N M) ∂d N)=q N M)
    (hcapture : ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ N in atTop, (∫ ω, (π N ω).real (Prod.mk ω ⁻¹' B N M)ᶜ ∂d N) < η)
    (hsize : ∀ M : ℝ, 0 < M → Tendsto (fun N => (Fintype.card (ιₙ N):ℝ)*q N M) atTop (𝓝 0)) :
    InProbability d (fun N ω => menuAllTimeDistance (P N ω) (ν N) (π N ω) (T N)) 1 := by
  have he : (fun N ω => menuAllTimeDistance (P N ω) (ν N) (π N ω) (T N)) =
      (fun N ω => menuDistance (fun j => evolvedKernel (Kernel.const (Ωₙ N) (ν N j)) (K N) ω) (π N ω)) := by
    funext N ω
    rw [menuAllTimeDistance_eq_endpoint _ _ _ (hcomp N ω) (hinv N ω)]
    congr 1
    funext j
    rw [evolvedKernel_apply,hK]
    rfl
  rw [he]
  exact prescribed_menu_endpoint_separation d ν π K B hB q hequal hcapture hsize

theorem inProbability_one_of_ge (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (f g : ∀ N, Ωₙ N → ℝ) (hf : InProbability d f 1)
    (hfg : ∀ N ω, f N ω ≤ g N ω) (hg : ∀ N ω, g N ω ≤ 1) : InProbability d g 1 := by
  intro ε hε
  apply squeeze_zero (fun N => measureReal_nonneg) _ (hf ε hε)
  intro N
  apply measureReal_mono
  intro ω hω
  change ε ≤ ‖g N ω-1‖ at hω
  change ε ≤ ‖f N ω-1‖
  have hf1 := (hfg N ω).trans (hg N ω)
  rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hf1)]
  rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (hg N ω))] at hω
  linarith [hfg N ω]
  all_goals finiteness

/-- Arbitrary field-dependent simplex weights are covered by the uniform
infimum. When the weights are Borel, selectedKernel realizes their actual
initial probability kernel. -/
theorem selected_endpoint_separation_of_uniform
    (d : ∀ N, Measure (Ωₙ N)) [∀ N, IsProbabilityMeasure (d N)]
    (μ : ∀ N, ιₙ N → Kernel (Ωₙ N) (Xₙ N)) [∀ N j, IsMarkovKernel (μ N j)]
    (π : ∀ N, Kernel (Ωₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (π N)]
    (K : ∀ N, Kernel (Ωₙ N × Xₙ N) (Xₙ N)) [∀ N, IsMarkovKernel (K N)]
    (w : ∀ N, Ωₙ N → Weights (ιₙ N)) (hw : ∀ N, Measurable (w N))
    (hmenu : InProbability d
      (fun N ω => menuDistance (fun j => evolvedKernel (μ N j) (K N) ω) (π N ω)) 1) :
    InProbability d (fun N ω => totalVariation
      (evolvedKernel (selectedKernel (μ N) (w N) (hw N)) (K N) ω) (π N ω)) 1 := by
  apply inProbability_one_of_ge d _ _ hmenu
  · intro N ω
    rw [evolved_selectedKernel]
    exact menuDistance_le _ _ (w N ω)
  · intro N ω
    exact totalVariation_le_one _ _

end Varying
end SlowEquilibration.ReductionFiniteMenu
