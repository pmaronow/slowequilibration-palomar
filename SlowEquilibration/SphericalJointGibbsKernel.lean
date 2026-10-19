-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalGibbsKernel

/-! Literal Gibbs kernels for arbitrary jointly continuous spherical
Hamiltonian families, including disorder, axis, and marks together. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SlowEquilibration.SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ} {Θ : Type*} [TopologicalSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ]

theorem jointHamiltonian_partition_measurable (β : ℝ) (H : Θ×Vector N→ℝ)
    (hH : Continuous H) : Measurable (fun p => partition N β (fun x => H (p,x))) := by
  exact (Real.continuous_exp.comp (hH.const_mul β)).stronglyMeasurable.integral_prod_right'.measurable

theorem jointHamiltonian_density_measurable (β : ℝ) (H : Θ×Vector N→ℝ)
    (hH : Continuous H) : Measurable (fun z : Θ×Vector N => gibbsDensity N β (fun x => H (z.1,x)) z.2) := by
  exact (Real.continuous_exp.comp (hH.const_mul β)).measurable.div
    ((jointHamiltonian_partition_measurable β H hH).comp measurable_fst)

def jointHamiltonianGibbsKernel (_hN : 1≤N) (β : ℝ) (H : Θ×Vector N→ℝ)
    (_hH : Continuous H) : Kernel Θ (Vector N) :=
  let _ := sphereLaw_probability N
  (Kernel.const Θ (sphereLaw N)).withDensity
    (fun p x => ENNReal.ofReal (gibbsDensity N β (fun y => H (p,y)) x))

theorem jointHamiltonianGibbsKernel_apply (hN : 1≤N) (β : ℝ) (H : Θ×Vector N→ℝ)
    (hH : Continuous H) (p : Θ) :
    jointHamiltonianGibbsKernel hN β H hH p=gibbsLaw N β (fun x => H (p,x)) := by
  let _ := sphereLaw_probability N
  unfold jointHamiltonianGibbsKernel
  rw [Kernel.withDensity_apply _ (jointHamiltonian_density_measurable β H hH).ennreal_ofReal]
  rfl

instance jointHamiltonianGibbsKernel_isMarkov (hN : 1≤N) (β : ℝ) (H : Θ×Vector N→ℝ)
    (hH : Continuous H) : IsMarkovKernel (jointHamiltonianGibbsKernel hN β H hH) where
  isProbabilityMeasure p := by
    rw [jointHamiltonianGibbsKernel_apply]
    exact gibbsLaw_probability hN β (hH.comp (continuous_const.prodMk continuous_id))

theorem jointHamiltonian_gibbsLaw_measurable (hN : 1≤N) (β : ℝ) (H : Θ×Vector N→ℝ)
    (hH : Continuous H) : Measurable (fun p => gibbsLaw N β (fun x => H (p,x))) := by
  have he : (fun p => gibbsLaw N β (fun x => H (p,x)))=
      fun p => jointHamiltonianGibbsKernel hN β H hH p :=
    funext (fun p => (jointHamiltonianGibbsKernel_apply hN β H hH p).symm)
  rw [he]
  exact (jointHamiltonianGibbsKernel hN β H hH).measurable

theorem jointHamiltonian_integral_measurable (hN : 1≤N) (β : ℝ) (H : Θ×Vector N→ℝ)
    (hH : Continuous H) (f : Θ×Vector N→ℝ) (hf : StronglyMeasurable f) :
    Measurable (fun p => ∫ x,f (p,x) ∂gibbsLaw N β (fun y => H (p,y))) := by
  have hi := hf.integral_kernel_prod_right' (κ:=jointHamiltonianGibbsKernel hN β H hH)
  simpa only [jointHamiltonianGibbsKernel_apply] using hi.measurable

end SlowEquilibration.SphericalModel
