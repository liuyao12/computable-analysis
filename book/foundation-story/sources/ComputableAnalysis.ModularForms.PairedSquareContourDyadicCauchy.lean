import ComputableAnalysis.ModularForms.PairedSquareDensityDyadicCauchy

/-! Fixed-radius Cauchy estimates for the entire oriented square average. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

def pairedSquareDyadicEdgeList (a : Scalar) (R : Rat) (n : Nat) : List HalfEdge → Scalar
  | [] => ⟨zero,ofQComplex_valid _⟩
  | edge::edges =>
    let h := pairedSquareDyadicAverage a edge R n
    let t := pairedSquareDyadicEdgeList a R n edges
    ⟨add h.val t.val,add_valid h.property t.property⟩

theorem sumPair_difference (a b c d : Scalar) :
    (add (sub a.val c.val) (sub b.val d.val)).Equiv
      (sub (add a.val b.val) (add c.val d.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (sub_valid a.property c.property) (sub_valid b.property d.property))
    (hright := sub_valid (add_valid a.property b.property) (add_valid c.property d.property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  change (A-C)+(B-D)=(A+B)-(C+D)
  grind only

theorem pairedSquareDyadicEdgeList_cauchy (a : Scalar) (R : Rat) (hR : 0<R)
    (eps : QPos) (edges : List HalfEdge) :
    ∃ N, ∀ n m, N≤n → N≤m →
      Small (sub (pairedSquareDyadicEdgeList a R n edges).val
        (pairedSquareDyadicEdgeList a R m edges).val) ((edges.length:Rat)*eps.val) := by
  induction edges with
  | nil =>
    refine ⟨0, ?_⟩
    intro n m hn hm
    have he : zero.Equiv (sub zero zero) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ofQComplex_valid _)
        (hright := sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
      change (0:ScalarAlgebra.Value)=0-0
      grind only
    have hb := Small.congr (ofQComplex_valid _)
      (sub_valid (ofQComplex_valid _) (ofQComplex_valid _)) he (Small.zero (Rat.le_refl (a:=0)))
    change Small (sub zero zero) (0*eps.val)
    rw [Rat.zero_mul]
    exact hb
  | cons edge edges ih =>
    obtain ⟨H,hH⟩ := pairedSquareDensity_dyadic_cauchy a edge R hR eps
    obtain ⟨T,hT⟩ := ih
    refine ⟨max H T, ?_⟩
    intro n m hn hm
    have hb := LocalODE.small_add (hH n m (by omega) (by omega))
      (hT n m (by omega) (by omega))
    have hd := Small.congr
      (add_valid
        (sub_valid (pairedSquareDyadicAverage a edge R n).property
          (pairedSquareDyadicAverage a edge R m).property)
        (sub_valid (pairedSquareDyadicEdgeList a R n edges).property
          (pairedSquareDyadicEdgeList a R m edges).property))
      (sub_valid (pairedSquareDyadicEdgeList a R n (edge::edges)).property
        (pairedSquareDyadicEdgeList a R m (edge::edges)).property)
      (sumPair_difference (pairedSquareDyadicAverage a edge R n)
        (pairedSquareDyadicEdgeList a R n edges) (pairedSquareDyadicAverage a edge R m)
        (pairedSquareDyadicEdgeList a R m edges)) hb
    have he : eps.val+(edges.length:Rat)*eps.val=((edge::edges).length:Rat)*eps.val := by
      rw [List.length_cons,Rat.natCast_add]
      change _=((edges.length:Rat)+1)*eps.val
      grind only
    rw [he] at hd
    exact hd

def pairedSquareDyadicContour (a : Scalar) (R : Rat) (n : Nat) : Scalar :=
  pairedSquareDyadicEdgeList a R n square

theorem pairedSquareDyadicContour_cauchy (a : Scalar) (R : Rat) (hR : 0<R)
    (eps : QPos) : ∃ N, ∀ n m, N≤n → N≤m →
      Small (sub (pairedSquareDyadicContour a R n).val
        (pairedSquareDyadicContour a R m).val) eps.val := by
  let e : QPos := ⟨eps.val/8, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (by decide +kernel)⟩
  obtain ⟨N,hN⟩ := pairedSquareDyadicEdgeList_cauchy a R hR e square
  refine ⟨N, ?_⟩
  intro n m hn hm
  have hb := hN n m hn hm
  have he : (square.length:Rat)*e.val=eps.val := by
    change 8*(eps.val/8)=eps.val
    grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.ModularForms
