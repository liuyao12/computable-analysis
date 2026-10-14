import ComputableAnalysis.RiemannHilbert.ReciprocalHolomorphic

/-! The two coordinate charts of the represented sphere. A name carries
either the finite coordinate or the coordinate at infinity. Equality on
the overlap is proved from reciprocal uniqueness; no completed complex
field or quotient completion is introduced. Topology and bundle
construction are handled in separate layers. -/
namespace ComputableAnalysis.RiemannHilbert.SphereCoordinates
open ComplexRaw NonzeroBoxSearch RepresentedReciprocal

inductive Name where
  | finite : Scalar → Name
  | infinity : Scalar → Name

def opposite (z w : Scalar) : Prop := (mul z.val w.val).Equiv (ofQComplex QComplex.one)

theorem opposite_symm (z w : Scalar) (hzw : opposite z w) : opposite w z :=
  equiv_trans (mul_valid w.property z.property) (mul_valid z.property w.property) (ofQComplex_valid _)
    (mul_comm_equiv _ _ w.property z.property) hzw

theorem opposite_congr (z z' w w' : Scalar) (hz : z.val.Equiv z'.val)
    (hw : w.val.Equiv w'.val) (hzw : opposite z w) : opposite z' w' :=
  equiv_trans (mul_valid z'.property w'.property) (mul_valid z.property w.property) (ofQComplex_valid _)
    (mul_equiv z'.property z.property w'.property w.property (equiv_symm hz) (equiv_symm hw)) hzw

theorem opposite_trans (z w u : Scalar) (hzw : opposite z w) (hwu : opposite w u) :
    z.val.Equiv u.val := unique w z u (opposite_symm z w hzw) hwu

def Equivalent : Name → Name → Prop
  | .finite z, .finite w => z.val.Equiv w.val
  | .infinity z, .infinity w => z.val.Equiv w.val
  | .finite z, .infinity w => opposite z w
  | .infinity z, .finite w => opposite z w

theorem equivalent_refl (p : Name) : Equivalent p p := by
  cases p with
  | finite z => exact equiv_refl _ z.property
  | infinity z => exact equiv_refl _ z.property

theorem equivalent_symm {p q : Name} (hpq : Equivalent p q) : Equivalent q p := by
  cases p <;> cases q
  · exact equiv_symm hpq
  · exact opposite_symm _ _ hpq
  · exact opposite_symm _ _ hpq
  · exact equiv_symm hpq

theorem equivalent_trans {p q r : Name} (hpq : Equivalent p q) (hqr : Equivalent q r) :
    Equivalent p r := by
  cases p with
  | finite p =>
    cases q with
    | finite q =>
      cases r with
      | finite r => exact equiv_trans p.property q.property r.property hpq hqr
      | infinity r => exact opposite_congr q p r r (equiv_symm hpq) (equiv_refl _ r.property) hqr
    | infinity q =>
      cases r with
      | finite r => exact opposite_trans p q r hpq hqr
      | infinity r => exact opposite_congr p p q r (equiv_refl _ p.property) hqr hpq
  | infinity p =>
    cases q with
    | finite q =>
      cases r with
      | finite r => exact opposite_congr p p q r (equiv_refl _ p.property) hqr hpq
      | infinity r => exact opposite_trans p q r hpq hqr
    | infinity q =>
      cases r with
      | finite r => exact opposite_congr q p r r (equiv_symm hpq) (equiv_refl _ r.property) hqr
      | infinity r => exact equiv_trans p.property q.property r.property hpq hqr

instance : Setoid Name where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

def finiteDomain : Name → Prop
  | .finite _ => True
  | .infinity w => Nonzero w

def infinityDomain : Name → Prop
  | .finite z => Nonzero z
  | .infinity _ => True

theorem domain_cover (p : Name) : finiteDomain p ∨ infinityDomain p := by
  cases p
  · exact Or.inl trivial
  · exact Or.inr trivial

theorem finiteDomain_congr {p q : Name} (hpq : p ≈ q) : finiteDomain p ↔ finiteDomain q := by
  cases p with
  | finite p =>
    cases q with
    | finite q => exact Iff.rfl
    | infinity q =>
      exact ⟨fun _ => nonzero_of_inverse q p (opposite_symm p q hpq), fun _ => trivial⟩
  | infinity p =>
    cases q with
    | finite q => exact ⟨fun _ => trivial, fun _ => nonzero_of_inverse p q hpq⟩
    | infinity q => exact nonzero_congr p q hpq

theorem infinityDomain_congr {p q : Name} (hpq : p ≈ q) : infinityDomain p ↔ infinityDomain q := by
  cases p with
  | finite p =>
    cases q with
    | finite q => exact nonzero_congr p q hpq
    | infinity q => exact ⟨fun _ => trivial, fun _ => nonzero_of_inverse p q hpq⟩
  | infinity p =>
    cases q with
    | finite q =>
      exact ⟨fun _ => nonzero_of_inverse q p (opposite_symm p q hpq), fun _ => trivial⟩
    | infinity q => exact Iff.rfl

def finiteCoordinate : (p : Name) → finiteDomain p → Scalar
  | .finite z, _ => z
  | .infinity w, hw => inverse w hw

def infinityCoordinate : (p : Name) → infinityDomain p → Scalar
  | .finite z, hz => inverse z hz
  | .infinity w, _ => w

theorem finiteCoordinate_congr {p q : Name} (hp : finiteDomain p) (hq : finiteDomain q)
    (hpq : p ≈ q) : (finiteCoordinate p hp).val.Equiv (finiteCoordinate q hq).val := by
  cases p with
  | finite p =>
    cases q with
    | finite q => exact hpq
    | infinity q => exact equiv_symm (inverse_unique q hq p (opposite_symm p q hpq))
  | infinity p =>
    cases q with
    | finite q => exact inverse_unique p hp q hpq
    | infinity q => exact inverse_congr p q hp hq hpq

theorem infinityCoordinate_congr {p q : Name} (hp : infinityDomain p) (hq : infinityDomain q)
    (hpq : p ≈ q) : (infinityCoordinate p hp).val.Equiv (infinityCoordinate q hq).val := by
  cases p with
  | finite p =>
    cases q with
    | finite q => exact inverse_congr p q hp hq hpq
    | infinity q => exact inverse_unique p hp q hpq
  | infinity p =>
    cases q with
    | finite q => exact equiv_symm (inverse_unique q hq p (opposite_symm p q hpq))
    | infinity q => exact hpq

theorem finiteCoordinate_name (p : Name) (hp : finiteDomain p) :
    Name.finite (finiteCoordinate p hp) ≈ p := by
  cases p with
  | finite p => exact equiv_refl _ p.property
  | infinity p => exact inverse_mul p hp

theorem infinityCoordinate_name (p : Name) (hp : infinityDomain p) :
    Name.infinity (infinityCoordinate p hp) ≈ p := by
  cases p with
  | finite p => exact inverse_mul p hp
  | infinity p => exact equiv_refl _ p.property

theorem overlap_inverse (p : Name) (hp : finiteDomain p) (hq : infinityDomain p) :
    opposite (finiteCoordinate p hp) (infinityCoordinate p hq) := by
  cases p with
  | finite p => exact mul_inverse p hq
  | infinity p => exact inverse_mul p hp

theorem finiteCoordinate_nonzero (p : Name) (hp : finiteDomain p) (hq : infinityDomain p) :
    Nonzero (finiteCoordinate p hp) :=
  nonzero_of_inverse _ _ (overlap_inverse p hp hq)

theorem infinityCoordinate_nonzero (p : Name) (hp : finiteDomain p) (hq : infinityDomain p) :
    Nonzero (infinityCoordinate p hq) :=
  nonzero_of_inverse _ _ (opposite_symm _ _ (overlap_inverse p hp hq))

theorem transition_value (p : Name) (hp : finiteDomain p) (hq : infinityDomain p) :
    (inverse (finiteCoordinate p hp) (finiteCoordinate_nonzero p hp hq)).val.Equiv
      (infinityCoordinate p hq).val :=
  inverse_unique _ _ _ (overlap_inverse p hp hq)

def atInfinity : Name := .infinity ⟨zero, ofQComplex_valid _⟩

theorem atInfinity_ne_finite (z : Scalar) : ¬ atInfinity ≈ Name.finite z := by
  intro hz
  have h := nonzero_of_inverse ⟨zero,ofQComplex_valid _⟩ z hz
  exact h (equiv_refl zero (ofQComplex_valid _))

end ComputableAnalysis.RiemannHilbert.SphereCoordinates
