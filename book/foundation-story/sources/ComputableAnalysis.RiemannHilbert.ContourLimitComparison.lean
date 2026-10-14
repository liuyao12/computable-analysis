import ComputableAnalysis.RiemannHilbert.ContourLocalFrames

/-! Proved stability of supplied sequence limits under scalar multiplication
and shrinking differences. Limit agreement is never a record field. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem product_difference_left (a p q : Scalar) :
    (sub (scalarProduct a p).val (scalarProduct a q).val).Equiv (mul a.val (sub p.val q.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scalarProduct a p).property (scalarProduct a q).property)
    (hright := mul_valid a.property (sub_valid p.property q.property))
  change gridScalarValue a*gridScalarValue p-gridScalarValue a*gridScalarValue q=
    gridScalarValue a*(gridScalarValue p-gridScalarValue q)
  grind only

theorem converge_product_left (a : Scalar) (p : Nat → Scalar) (q : Scalar) (hp : Converges p q) :
    Converges (fun n => scalarProduct a (p n)) (scalarProduct a q) := by
  intro eps
  let C : QPos := ⟨2*scalarBound a,Rat.mul_pos (by decide +kernel) (scalarBound_pos a)⟩
  let eta := divideRadius eps C
  obtain ⟨N,hN⟩ := hp eta
  refine ⟨N, ?_⟩
  intro n hn
  have hb := Small.mul a.property (sub_valid (p n).property q.property)
    (Rat.le_of_lt (scalarBound_pos a)) (Rat.le_of_lt eta.property) (scalar_small a) (hN n hn)
  have he : 2*scalarBound a*eta.val=eps.val := divideRadius_identity eps C
  rw [he] at hb
  exact Small.congr (mul_valid a.property (sub_valid (p n).property q.property))
    (sub_valid (scalarProduct a (p n)).property (scalarProduct a q).property)
    (equiv_symm (product_difference_left a (p n) q)) hb

theorem converge_perturbation (p q : Nat → Scalar) (a : Scalar) (hq : Converges q a)
    (he : ∀ eps : QPos, ∃ N, ∀ n, N≤n → Small (sub (p n).val (q n).val) eps.val) :
    Converges p a := by
  intro eps
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  obtain ⟨A,hA⟩ := hq eta
  obtain ⟨B,hB⟩ := he eta
  refine ⟨max A B, ?_⟩
  intro n hn
  have hb := LocalODE.small_add (hB n (by omega)) (hA n (by omega))
  have heps : eta.val+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at h
    grind only
  rw [heps] at hb
  exact Small.congr (add_valid (sub_valid (p n).property (q n).property)
    (sub_valid (q n).property a.property)) (sub_valid (p n).property a.property)
    (representedDifference_split (p n) (q n) a) hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
