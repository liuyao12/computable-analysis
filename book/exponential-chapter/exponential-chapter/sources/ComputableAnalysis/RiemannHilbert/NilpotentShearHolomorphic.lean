import ComputableAnalysis.RiemannHilbert.NilpotentShear
import ComputableAnalysis.RiemannHilbert.TranslatedHolomorphic

/-! Actual holomorphic coordinates of the varying shear and its inverse.
The affine difference identities prove zero derivative errors in every complex
direction, and the constant derivatives have explicit continuity witnesses. -/
namespace ComputableAnalysis.RiemannHilbert.NilpotentShear
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def shifted (N : ValueMap (Fiber n) (Fiber n)) (c z : Scalar) :=
  forward N (Centered.offset c z)

def shiftedInverse (N : ValueMap (Fiber n) (Fiber n)) (c z : Scalar) :=
  backward N (Centered.offset c z)

theorem shifted_congr (N : ValueMap (Fiber n) (Fiber n)) (c z w : Scalar)
    (hzw : z.val.Equiv w.val) : (shifted N c z).Equiv (shifted N c w) :=
  forward_congr N _ _ (Centered.offset_congr c c z w (equiv_refl _ c.property) hzw)

theorem shiftedInverse_congr (N : ValueMap (Fiber n) (Fiber n)) (c z w : Scalar)
    (hzw : z.val.Equiv w.val) : (shiftedInverse N c z).Equiv (shiftedInverse N c w) :=
  fun x => Fiber.sub_congr (Setoid.refl x) (Fiber.scale_congr
    (Centered.offset_congr c c z w (equiv_refl _ c.property) hzw) (Setoid.refl (N.eval x)))

theorem shifted_difference (N : ValueMap (Fiber n) (Fiber n)) (c w z : Scalar) (x : Fiber n) :
    Fiber.sub ((shifted N c z).eval x) ((shifted N c w).eval x) ≈
      Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ (N.eval x) := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Fiber.sub ((shifted N c z).eval x) ((shifted N c w).eval x)).property i)
    (hright := (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ (N.eval x)).property i)
  change
    (ComplexRawQuotient.ofRaw (x.val i) (x.property i) +
      (ComplexRawQuotient.ofRaw z.val z.property - ComplexRawQuotient.ofRaw c.val c.property) *
        ComplexRawQuotient.ofRaw ((N.eval x).val i) ((N.eval x).property i)) -
    (ComplexRawQuotient.ofRaw (x.val i) (x.property i) +
      (ComplexRawQuotient.ofRaw w.val w.property - ComplexRawQuotient.ofRaw c.val c.property) *
        ComplexRawQuotient.ofRaw ((N.eval x).val i) ((N.eval x).property i)) =
    (ComplexRawQuotient.ofRaw z.val z.property - ComplexRawQuotient.ofRaw w.val w.property) *
      ComplexRawQuotient.ofRaw ((N.eval x).val i) ((N.eval x).property i)
  grind

theorem shiftedInverse_difference (N : ValueMap (Fiber n) (Fiber n)) (c w z : Scalar) (x : Fiber n) :
    Fiber.sub ((shiftedInverse N c z).eval x) ((shiftedInverse N c w).eval x) ≈
      Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ (Fiber.neg (N.eval x)) := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Fiber.sub ((shiftedInverse N c z).eval x) ((shiftedInverse N c w).eval x)).property i)
    (hright := (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ (Fiber.neg (N.eval x))).property i)
  change
    (ComplexRawQuotient.ofRaw (x.val i) (x.property i) -
      (ComplexRawQuotient.ofRaw z.val z.property - ComplexRawQuotient.ofRaw c.val c.property) *
        ComplexRawQuotient.ofRaw ((N.eval x).val i) ((N.eval x).property i)) -
    (ComplexRawQuotient.ofRaw (x.val i) (x.property i) -
      (ComplexRawQuotient.ofRaw w.val w.property - ComplexRawQuotient.ofRaw c.val c.property) *
        ComplexRawQuotient.ofRaw ((N.eval x).val i) ((N.eval x).property i)) =
    (ComplexRawQuotient.ofRaw z.val z.property - ComplexRawQuotient.ofRaw w.val w.property) *
      (-ComplexRawQuotient.ofRaw ((N.eval x).val i) ((N.eval x).property i))
  grind

theorem shifted_remainder_zero (N : ValueMap (Fiber n) (Fiber n)) (c : Scalar)
    (D : Scalar → Prop) (w z : Scalar) (hw : D w) (hz : D z) (x : Fiber n) :
    CoordinateBound (LinearField.operatorRemainder
      (fun z _ => shifted N c z) (fun _ _ => N) w z hw hz x) 0 :=
  Fiber.sub_zero_bound (shifted_difference N c w z x)

theorem shifted_uniform_remainder (N : ValueMap (Fiber n) (Fiber n)) (c : Scalar)
    (D : Scalar → Prop) (eps H : QPos) (w z : Scalar) (hw : D w) (hz : D z)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) :
    CoordinateBound (LinearField.operatorRemainder
      (fun z _ => shifted N c z) (fun _ _ => N) w z hw hz x) ((eps.val*H.val)*E) :=
  fun i => (shifted_remainder_zero N c D w z hw hz x i).mono
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property)) hE)

def affineCoordinate (f : Scalar → Fiber n)
    (hcongr : ∀ z w, z.val.Equiv w.val → f z ≈ f w) (i : Fin n) : CertifiedFunctions.Map where
  domain _ := True
  eval z := (f z).val i
  valid z _ := (f z).property i
  domain_congr _ _ _ := Iff.rfl
  eval_congr z w _ _ hzw := hcongr z w hzw i

def affineCoordinate_holomorphic (f : Scalar → Fiber n)
    (hcongr : ∀ z w, z.val.Equiv w.val → f z ≈ f w) (d : Fiber n)
    (hdiff : ∀ w z, Fiber.sub (f z) (f w) ≈
      Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ d)
    (i : Fin n) : CertifiedFunctions.Holomorphic (affineCoordinate f hcongr i) where
  openDomain := {
    radius := fun _ _ => ⟨1, by decide +kernel⟩
    inside := fun _ _ _ _ => True.intro }
  derivative _ := d.val i
  atPoint w _ := {
    point_mem := True.intro
    derivative_valid := d.property i
    delta := fun _ => ⟨1, by decide +kernel⟩
    estimate := fun eps H z _ _ _ => by
      have he : Fiber.sub (f z) (f w) ≈
          ⟨fun j => mul (d.val j) (sub z.val w.val),
            fun j => mul_valid (d.property j) (sub_valid z.property w.property)⟩ :=
        Setoid.trans (hdiff w z) (fun j =>
          mul_comm_equiv _ _ (sub_valid z.property w.property) (d.property j))
      exact (Fiber.sub_zero_bound he i).mono
        (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property)) }
  derivative_congr _ _ _ _ _ := equiv_refl _ (d.property i)
  continuousDerivative := {
    delta := fun _ _ _ => ⟨1, by decide +kernel⟩
    estimate := fun _ _ eps _ _ _ =>
      (Fiber.sub_zero_bound (Setoid.refl d) i).mono (Rat.le_of_lt eps.property) }

def coordinate (N : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (x : Fiber n) (i : Fin n) :=
  affineCoordinate (fun z => (shifted N c z).eval x) (fun z w hzw => shifted_congr N c z w hzw x) i

def coordinate_holomorphic (N : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (x : Fiber n) (i : Fin n) :
    CertifiedFunctions.Holomorphic (coordinate N c x i) :=
  affineCoordinate_holomorphic _ _ (N.eval x) (fun w z => shifted_difference N c w z x) i

def inverseCoordinate (N : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (x : Fiber n) (i : Fin n) :=
  affineCoordinate (fun z => (shiftedInverse N c z).eval x)
    (fun z w hzw => shiftedInverse_congr N c z w hzw x) i

def inverseCoordinate_holomorphic (N : ValueMap (Fiber n) (Fiber n)) (c : Scalar) (x : Fiber n) (i : Fin n) :
    CertifiedFunctions.Holomorphic (inverseCoordinate N c x i) :=
  affineCoordinate_holomorphic _ _ (Fiber.neg (N.eval x))
    (fun w z => shiftedInverse_difference N c w z x) i

end ComputableAnalysis.RiemannHilbert.NilpotentShear
