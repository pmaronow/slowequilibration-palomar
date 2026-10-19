-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedLineCurvature

@[expose] public section

/-! Every segment in the manuscript's single source-chosen mixed rectangle
has the uniform negative second derivative needed for the joint Gaussian
Laplace comparison. -/

namespace SlowEquilibration.SphericalTAPMixedLineUniformCurvature
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open SphericalTAPMixedBandExponent SphericalTAPMixedLineCurvature
open SphericalTAPMixedJointHessianNeighborhood
open SphericalTAPMixedCommonAnalyticChoice
set_option autoImplicit false

private theorem affine_mem_Icc {L R k0 k1 t : ℝ}
    (hk0 : k0 ∈ Icc L R) (hk1 : k1 ∈ Icc L R)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    k0+(k1-k0)*t ∈ Icc L R := by
  have hs : k0+t • (k1-k0) ∈ Icc L R :=
    (convex_Icc L R).add_smul_mem hk0 (by convert hk1 using 1; ring) ht
  simpa only [smul_eq_mul,mul_comm t (k1-k0)] using hs

/-- From the literal source certificate, choose one physical mixed rectangle
on which every affine line has a uniform strictly negative second
derivative. This uses the actual `g`, not an abstract Hessian surrogate. -/
theorem mixed_source_line_uniform_curvature
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    let edge := 2*Real.sqrt (Q^2*μ.xi2 Q)
    ∃ L R ε0 b0 cstar : ℝ,
      0 < ε0 ∧ 0 < b0 ∧ 0 < cstar ∧ edge < L ∧ L < K ∧ K < R ∧
      Icc (q-b0) (q+b0) ⊆ Ioo (0 : ℝ) 1 ∧
      ∀ e ∈ Icc (E-ε0) (E+ε0),
        ∀ k0 ∈ Icc L R, ∀ k1 ∈ Icc L R,
          ∀ a0 ∈ Icc (q-b0) (q+b0),
            ∀ a1 ∈ Icc (q-b0) (q+b0),
              ∀ t ∈ Icc (0 : ℝ) 1,
                deriv (deriv (fun s => sourceMixedBandExponent μ β Q e
                  (k0+(k1-k0)*s) (a0+(a1-a0)*s))) t ≤
                    -cstar*((k1-k0)^2+(a1-a0)^2) := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  obtain ⟨L,R,ε0,b0,ε2,cstar,hε0,hb0,_,_,_,hcstar,
    hedge,hLK,hKR,hI,_,_,hH⟩ := mixed_source_common_analytic_choice μ h hnp
  refine ⟨L,R,ε0,b0,cstar,hε0,hb0,hcstar,hedge,hLK,hKR,hI,?_⟩
  intro e he k0 hk0 k1 hk1 a0 ha0 a1 ha1 t ht
  have hkt : k0+(k1-k0)*t ∈ Icc L R := affine_mem_Icc hk0 hk1 ht
  have hat : a0+(a1-a0)*t ∈ Icc (q-b0) (q+b0) :=
    affine_mem_Icc ha0 ha1 ht
  have hphysical : |a0+(a1-a0)*t| < 1 := by
    have hh := hI hat
    exact abs_lt.mpr ⟨by linarith [hh.1],hh.2⟩
  have hexterior : 2*Real.sqrt (Q^2*μ.xi2 Q) < k0+(k1-k0)*t :=
    lt_of_lt_of_le hedge hkt.1
  rw [mixed_line_second μ β h.overlap_range.1 e k0 a0 (k1-k0) (a1-a0) t
    hexterior hphysical]
  exact hH e he (k0+(k1-k0)*t) hkt (a0+(a1-a0)*t) hat
    (k1-k0) (a1-a0)

end
end SlowEquilibration.SphericalTAPMixedLineUniformCurvature
