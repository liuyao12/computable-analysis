import ComputableAnalysis.ModularForms.RationalReciprocalBound

/-! Uniform numerator bounds and reciprocal decay on rational upper-half-plane regions. -/
namespace ComputableAnalysis.ModularForms

private theorem product_box (a b A B : Rat) (_hA : 0≤A) (hB : 0≤B)
    (ha : -A≤a ∧ a≤A) (hb : -B≤b ∧ b≤B) : -A*B≤a*b ∧ a*b≤A*B := by
  by_cases hp : 0≤a
  · have hl := Rat.mul_le_mul_of_nonneg_left hb.1 hp
    have hu := Rat.mul_le_mul_of_nonneg_left hb.2 hp
    have hs := Rat.mul_le_mul_of_nonneg_right ha.2 hB
    grind
  · have hn : 0≤ -a := by grind
    have hl := Rat.mul_le_mul_of_nonneg_left hb.1 hn
    have hu := Rat.mul_le_mul_of_nonneg_left hb.2 hn
    have hs := Rat.mul_le_mul_of_nonneg_right (show -a≤A by grind) hB
    grind

theorem rationalLattice_numerator_bounds (z : QComplex) (x y r R H : Rat)
    (hr : 0≤r) (hR : 0≤R) (hH : 0≤H)
    (hx : -r≤x ∧ x≤r) (hy : -r≤y ∧ y≤r)
    (hre : -R≤z.re ∧ z.re≤R) (him : -H≤z.im ∧ z.im≤H) :
    (-(1+R+H)*r≤x+y*z.re ∧ x+y*z.re≤(1+R+H)*r) ∧
    (-(1+R+H)*r≤ -(y*z.im) ∧ -(y*z.im)≤(1+R+H)*r) := by
  have ha := product_box y z.re r R hr hR hy hre
  have hb := product_box y z.im r H hr hH hy him
  have hrr := Rat.mul_nonneg hr hR
  have hrh := Rat.mul_nonneg hr hH
  grind

/-- All reciprocal-coordinate bounds follow solely from regional and index boxes. -/
theorem rationalLattice_box_reciprocal_bounds (z : QComplex) (x y r R H eta : Rat)
    (hr : 0<r) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hx : -r≤x ∧ x≤r) (hy : -r≤y ∧ y≤r)
    (hre : -R≤z.re ∧ z.re≤R) (him : eta≤z.im ∧ z.im≤H)
    (hout : r≤x ∨ x≤ -r ∨ r≤y ∨ y≤ -r) :
    let N := rationalLatticeNorm z x y
    let L := (2*eta*eta+2*R*R+1)*(1+R+H)/(eta*eta)/r
    (-L≤(x+y*z.re)/N ∧ (x+y*z.re)/N≤L) ∧
      (-L≤ -(y*z.im)/N ∧ -(y*z.im)/N≤L) := by
  have hi : -H≤z.im := by grind
  have hb := rationalLattice_numerator_bounds z x y r R H (Rat.le_of_lt hr) hR hH hx hy hre ⟨hi,him.2⟩
  exact rationalLattice_reciprocal_bounds z x y r R eta (1+R+H) hr hR heta
    (by grind) hre him.1 hout hb.1 hb.2

open RiemannHilbert

def latticeRegionHeight (z : Scalar) (hz : InUpperHalfPlane z.val) : Rat :=
  qabs (z.val.compute (latticeRegionStage z hz)).hi.im+1

theorem latticeRegionHeight_nonnegative (z : Scalar) (hz : InUpperHalfPlane z.val) :
    0≤latticeRegionHeight z hz := by
  have h := qabs_nonneg (z.val.compute (latticeRegionStage z hz)).hi.im
  unfold latticeRegionHeight
  grind

theorem latticeRegion_sample_height (z : Scalar) (hz : InUpperHalfPlane z.val)
    (n : Nat) (hn : latticeRegionStage z hz≤n) (q : QComplex)
    (hq : (z.val.compute n).lo≤q ∧ q≤(z.val.compute n).hi) : q.im≤latticeRegionHeight z hz := by
  have hb := ComplexRaw.valid_nestedIn z.property hn
  have hh := self_le_qabs (z.val.compute (latticeRegionStage z hz)).hi.im
  have hc := Rat.le_trans hq.2.2 hb.2.2
  unfold latticeRegionHeight
  grind

end ComputableAnalysis.ModularForms
