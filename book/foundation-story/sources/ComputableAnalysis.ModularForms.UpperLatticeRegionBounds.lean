import ComputableAnalysis.ModularForms.RationalLatticeCoercivity

/-! Uniform lattice lower bounds for rational samples in represented upper-half-plane boxes. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

/-- Coordinate bounds on one supplied interval stage; no lattice conclusion is
included in this evidence. Later valid stages inherit these region bounds. -/
structure LatticeRegionBox (z : Scalar) (R eta : Rat) (N : Nat) : Prop where
  real_lower : -R≤(z.val.compute N).lo.re
  real_upper : (z.val.compute N).hi.re≤R
  imag_lower : eta≤(z.val.compute N).lo.im

theorem latticeRegion_sample (z : Scalar) (R eta : Rat) (N n : Nat)
    (h : LatticeRegionBox z R eta N) (hn : N≤n) (q : QComplex)
    (hq : (z.val.compute n).lo≤q ∧ q≤(z.val.compute n).hi) :
    (-R≤q.re ∧ q.re≤R) ∧ eta≤q.im := by
  have hb := ComplexRaw.valid_nestedIn z.property hn
  exact ⟨⟨Rat.le_trans h.real_lower (Rat.le_trans hb.1.1 hq.1.1),
    Rat.le_trans hq.2.1 (Rat.le_trans hb.2.1 h.real_upper)⟩,
    Rat.le_trans h.imag_lower (Rat.le_trans hb.1.2 hq.1.2)⟩

/-- Coercivity holds uniformly for every rational point of every later box. -/
theorem latticeRegion_sample_coercive (z : Scalar) (R eta : Rat) (N n : Nat)
    (hR : 0≤R) (heta : 0<eta) (h : LatticeRegionBox z R eta N) (hn : N≤n)
    (q : QComplex) (hq : (z.val.compute n).lo≤q ∧ q≤(z.val.compute n).hi)
    (x y : Rat) :
    eta*eta*(x*x+y*y)≤(2*eta*eta+2*R*R+1)*rationalLatticeNorm q x y := by
  have hs := latticeRegion_sample z R eta N n h hn q hq
  exact rationalLattice_coercive q x y R eta hR heta hs.1 hs.2

/-- The regional lower bound applies uniformly to all outside-square lattice indices. -/
theorem latticeRegion_sample_outside_square (z : Scalar) (R eta : Rat) (N n : Nat)
    (hR : 0≤R) (heta : 0<eta) (h : LatticeRegionBox z R eta N) (hn : N≤n)
    (q : QComplex) (hq : (z.val.compute n).lo≤q ∧ q≤(z.val.compute n).hi)
    (x y r : Rat) (hr : 0≤r) (hout : r≤x ∨ x≤ -r ∨ r≤y ∨ y≤ -r) :
    eta*eta*r*r≤(2*eta*eta+2*R*R+1)*rationalLatticeNorm q x y := by
  have hs := latticeRegion_sample z R eta N n h hn q hq
  exact rationalLattice_outside_square q x y r R eta hr hR heta hs.1 hs.2 hout

end ComputableAnalysis.ModularForms
