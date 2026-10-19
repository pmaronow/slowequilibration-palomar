-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SemicircleQuadraticTangent

/-! A genuine one-dimensional global quadratic contact bound for the pure
scalar semicircle complexity, valid across the whole GOE support. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PureScalarComplexityGeometry
open Set
set_option maxHeartbeats 400000

def profile (V b p c e : ℝ) : ℝ :=
  c-e^2/(2*V)+SemicirclePotential.potential (p*e/Real.sqrt b)

def curvature (V b p : ℝ) : ℝ := 1/V-p^2/(2*b)

theorem profile_contact_loss {V b p c E0 c0 : ℝ} (hV : 0 < V) (hb : 0 < b)
    (hEdge : 2 < p*E0/Real.sqrt b) (hZero : profile V b p c E0=0)
    (hSlope : -E0/V+p/Real.sqrt b*SemicirclePotential.resolvent (p*E0/Real.sqrt b)=-c0)
    (e : ℝ) :
    profile V b p c e ≤ -c0*(e-E0)-curvature V b p/2*(e-E0)^2 := by
  have hS := Real.sqrt_pos.mpr hb
  have hS2 := Real.sq_sqrt hb.le
  have hOmega := SemicirclePotential.potential_global_quadratic_tangent hEdge (p*e/Real.sqrt b)
  have hDifference : p*e/Real.sqrt b-p*E0/Real.sqrt b=p*(e-E0)/Real.sqrt b := by ring
  rw [hDifference] at hOmega
  have hRemainder : SemicirclePotential.potential (p*e/Real.sqrt b)-SemicirclePotential.potential (p*E0/Real.sqrt b)-
      SemicirclePotential.resolvent (p*E0/Real.sqrt b)*(p*(e-E0)/Real.sqrt b)-
      (p*(e-E0)/Real.sqrt b)^2/4 ≤ 0 := by linarith
  have hIdentity : profile V b p c e=
      profile V b p c E0+
      (-E0/V+p/Real.sqrt b*SemicirclePotential.resolvent (p*E0/Real.sqrt b))*(e-E0)-
      curvature V b p/2*(e-E0)^2+
      (SemicirclePotential.potential (p*e/Real.sqrt b)-SemicirclePotential.potential (p*E0/Real.sqrt b)-
        SemicirclePotential.resolvent (p*E0/Real.sqrt b)*(p*(e-E0)/Real.sqrt b)-
        (p*(e-E0)/Real.sqrt b)^2/4) := by
    unfold profile curvature
    field_simp [hV.ne',hb.ne',hS.ne']
    ring_nf
    rw [hS2]
    ring
  rw [hIdentity,hZero,hSlope]
  linarith
end SlowEquilibration.PureScalarComplexityGeometry
