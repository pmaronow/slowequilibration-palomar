-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.Upstream.OAI.Computability.MinUncut.GaussianHermite

/-! Genuine L² Gaussian Mehler noise and every Hermite coefficient. The
pinned source's bounded-test restriction is removed by actual product-L²
Cauchy–Schwarz, retaining the true rotated Gaussian law. -/
@[expose] public section
namespace SlowEquilibration.GaussianMaximalCorrelation
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped ENNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {ι : Type*} [Fintype ι]

lemma coupled_memLp (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : MemLp Q 2 (γpi ι)) :
    MemLp (fun z : (ι → ℝ)×(ι → ℝ) => Q (ρ • z.1+s • z.2)) 2 ((γpi ι).prod (γpi ι)) := by
  exact (hQ.comp_fst (γpi ι)).comp_measurePreserving (rotation_preserves ρ s h)

/-- The actual conditional Gaussian average is in L² for every L² test. -/
theorem memLp_noise_L2 (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hQ2 : MemLp Q 2 (γpi ι)) : MemLp (noise ρ s Q) 2 (γpi ι) := by
  have hrot:=coupled_memLp ρ s h hQ2
  have hsq:=hrot.integrable_sq
  apply (memLp_two_iff_integrable_sq (measurable_noise ρ s hQ).aestronglyMeasurable).mpr
  apply Integrable.mono hsq.integral_prod_left
    ((measurable_noise ρ s hQ).pow_const 2).aestronglyMeasurable
  filter_upwards [hsq.prod_right_ae] with x hx
  have hx2 : MemLp (fun y : ι → ℝ => Q (ρ • x+s • y)) 2 (γpi ι) :=
    (memLp_two_iff_integrable_sq (hQ.comp (by fun_prop)).aestronglyMeasurable).mpr hx
  have hv:=variance_nonneg (fun y : ι → ℝ => Q (ρ • x+s • y)) (γpi ι)
  rw [variance_eq_sub hx2] at hv
  change |(∫ y,Q (ρ • x+s • y) ∂γpi ι)^2| ≤ |∫ y,Q (ρ • x+s • y)^2 ∂γpi ι|
  rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (integral_nonneg (fun y => sq_nonneg (Q (ρ • x+s • y))))]
  exact sub_nonneg.mp hv

/-- Every Hermite noise coefficient, proved by a true Gaussian rotation;
no bound on Q or a desired contraction conclusion is assumed. -/
theorem noise_coefficient_L2 (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hQ2 : MemLp Q 2 (γpi ι)) (a : ι → ℕ) :
    coeff (noise ρ s Q) a=ρ^(degree a)*coeff Q a := by
  let μ:=(γpi ι).prod (γpi ι)
  let f:((ι → ℝ)×(ι → ℝ)) → ℝ:=fun z => psi a z.1*Q (ρ • z.1+s • z.2)
  have hqm : Measurable (fun z : (ι → ℝ)×(ι → ℝ) => Q (ρ • z.1+s • z.2)) := hQ.comp (by fun_prop)
  have hfm : Measurable f := ((continuous_psi a).measurable.comp measurable_fst).mul hqm
  have hfi : Integrable f μ := (memLp_psi a |>.comp_fst (γpi ι)).integrable_mul (coupled_memLp ρ s h hQ2)
  have hm:=rotation_preserves (ι:=ι) ρ s h
  have hfi' : Integrable (f ∘ rotation ρ s) μ := (hm.integrable_comp hfm.aestronglyMeasurable).mpr hfi
  have htrans (z : (ι → ℝ)×(ι → ℝ)) : f (rotation ρ s z)=Q z.1*psi a (ρ • z.1+s • z.2) := by
    have hx:=congrArg Prod.fst (rotation_involutive (ι:=ι) ρ s h z)
    change ρ • (ρ • z.1+s • z.2)+s • (s • z.1-ρ • z.2)=z.1 at hx
    dsimp [f,OAI.MinUncut.GaussianHermite.rotation_apply]
    rw [hx,mul_comm]
  change (∫ x,psi a x*noise ρ s Q x ∂γpi ι)=ρ^(∑ i,a i)*(∫ x,psi a x*Q x ∂γpi ι)
  calc
    _ = ∫ z,f z ∂μ := by
      rw [integral_prod _ hfi]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_const_mul _ _).symm
    _ = ∫ z,f (rotation ρ s z) ∂μ := by
      simpa only [hm.map_eq] using
        (integral_map (μ:=(γpi ι).prod (γpi ι)) hm.measurable.aemeasurable hfm.aestronglyMeasurable)
    _ = ∫ x,∫ y,Q x*psi a (ρ • x+s • y) ∂γpi ι ∂γpi ι := by
      change (∫ z,(f ∘ rotation ρ s) z ∂(γpi ι).prod (γpi ι))=_
      rw [integral_prod _ hfi']
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      exact htrans (x,y)
    _ = _ := by
      simp only [integral_const_mul,show ∀ x y : ι → ℝ,ρ • x+s • y=fun i => ρ*x i+s*y i by intros;rfl,
        psi_noise ρ s h]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

end
end SlowEquilibration.GaussianMaximalCorrelation
