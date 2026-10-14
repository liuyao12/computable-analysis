import ComputableAnalysis.ModularForms.InnerSquareContourAssembly

/-! Two Cartesian sample segments assemble into one doubled half-edge grid. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem gridScalarSum_append (f : Nat → Scalar) (M N : Nat) :
    (scalarSum (gridScalarSum M f) (gridScalarSum N (fun v => f (M+v)))).val.Equiv
      (gridScalarSum (M+N) f).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarSum (gridScalarSum M f) (gridScalarSum N (fun v => f (M+v)))).property)
    (hright := (gridScalarSum (M+N) f).property)
  change gridScalarValue (scalarSum _ _)=gridScalarValue (gridScalarSum (M+N) f)
  simp only [gridScalarValue_add,gridScalarSum_value]
  exact (gridValueSum_append (fun v => gridScalarValue (f v)) M N).symm

theorem squareMidpointSum_concat (f : Rat → Scalar) (M : Nat) (hM : 0<M) :
    (scalarSum
      (gridScalarSum M (fun v => f (squareMidpointParameter M v/2)))
      (gridScalarSum M (fun v => f ((1+squareMidpointParameter M v)/2)))).val.Equiv
      (gridScalarSum (2*M) (fun v => f (squareMidpointParameter (2*M) v))).val := by
  have h0 (v : Nat) : squareMidpointParameter M v/2=squareMidpointParameter (2*M) v := by
    have h := squareMidpointParameter_concat M 0 v hM
    simp only [Nat.zero_mul,Nat.zero_add] at h
    change (0+squareMidpointParameter M v)/2=_ at h
    simpa only [Rat.zero_add] using h
  have h1 (v : Nat) : (1+squareMidpointParameter M v)/2=squareMidpointParameter (2*M) (M+v) := by
    have h := squareMidpointParameter_concat M 1 v hM
    simp only [Nat.one_mul] at h
    exact h
  have ha := add_equiv
    (gridScalarSum_congr M (fun v => f (squareMidpointParameter M v/2))
      (fun v => f (squareMidpointParameter (2*M) v)) (fun v => by rw [h0]; exact equiv_refl _ (f _).property))
    (gridScalarSum_congr M (fun v => f ((1+squareMidpointParameter M v)/2))
      (fun v => f (squareMidpointParameter (2*M) (M+v))) (fun v => by rw [h1]; exact equiv_refl _ (f _).property))
  have hb := gridScalarSum_append (fun v => f (squareMidpointParameter (2*M) v)) M M
  have he : M+M=2*M := by omega
  rw [he] at hb
  exact equiv_trans
    (scalarSum (gridScalarSum M (fun v => f (squareMidpointParameter M v/2)))
      (gridScalarSum M (fun v => f ((1+squareMidpointParameter M v)/2)))).property
    (scalarSum (gridScalarSum M (fun v => f (squareMidpointParameter (2*M) v)))
      (gridScalarSum M (fun v => f (squareMidpointParameter (2*M) (M+v))))).property
    (gridScalarSum (2*M) (fun v => f (squareMidpointParameter (2*M) v))).property ha hb

def weightedMidpointSum (f : Rat → Scalar) (M : Nat) (r : Rat) : Scalar :=
  let terms := gridScalarSum M (fun v => f (squareMidpointParameter M v))
  ⟨scaleRat r terms.val,scaleRat_valid terms.property⟩

theorem weightedSquareMidpointSum_concat (f : Rat → Scalar) (M : Nat) (hM : 0<M) (r : Rat) :
    (scalarSum (weightedMidpointSum (fun u => f (u/2)) M r)
      (weightedMidpointSum (fun u => f ((1+u)/2)) M r)).val.Equiv
      (weightedMidpointSum f (2*M) r).val := by
  let A := gridScalarSum M (fun v => f (squareMidpointParameter M v/2))
  let B := gridScalarSum M (fun v => f ((1+squareMidpointParameter M v)/2))
  have ha := scaleRat_add_equiv r A.val B.val A.property B.property
  have hb := representedScale_congr (scalarSum A B)
    (gridScalarSum (2*M) (fun v => f (squareMidpointParameter (2*M) v))) r
    (squareMidpointSum_concat f M hM)
  exact equiv_trans
    (scalarSum (weightedMidpointSum (fun u => f (u/2)) M r)
      (weightedMidpointSum (fun u => f ((1+u)/2)) M r)).property
    (scaleRat_valid (scalarSum A B).property)
    (weightedMidpointSum f (2*M) r).property (equiv_symm ha) hb

open PDE.CauchyContour

theorem cartesianHalfEdgeSum_split (c : Scalar) (quarter : Quarter) (S : Rat)
    (M : Nat) (hM : 0<M) (upper : Bool) :
    (scalarSum
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨quarter,true⟩ S
        (if upper then u/2 else u/2-1)) M (((2*M:Nat):Rat)⁻¹))
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨quarter,true⟩ S
        (if upper then (1+u)/2 else (1+u)/2-1)) M (((2*M:Nat):Rat)⁻¹))).val.Equiv
      (cartesianHalfEdgeSum c quarter S (2*M) upper).val := by
  have h := weightedSquareMidpointSum_concat
    (fun u => pairedSquareDensitySample c ⟨quarter,true⟩ S (if upper then u else u-1))
    M hM (((2*M:Nat):Rat)⁻¹)
  exact h

end ComputableAnalysis.ModularForms

