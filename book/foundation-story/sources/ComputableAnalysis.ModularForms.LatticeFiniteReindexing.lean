import ComputableAnalysis.RiemannHilbert.LocalODECoefficients
import ComputableAnalysis.RiemannHilbert.ScalarAlgebra
import ComputableAnalysis.ModularForms.CMLatticePowerConjugation163

/-! Exact finite reindexing for executable represented complex sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert
set_option maxHeartbeats 800000

private def indexSum {α : Type} (f : α → ScalarAlgebra.Value) : List α → ScalarAlgebra.Value
  | [] => 0
  | a :: as => f a+indexSum f as

private theorem indexSum_perm {α : Type} (f : α → ScalarAlgebra.Value)
    {as bs : List α} (h : as.Perm bs) : indexSum f as=indexSum f bs := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [indexSum,ih]
  | swap a b as => simp only [indexSum]; grind
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

private theorem indexSum_raw {α : Type} (f : α → ComplexRaw)
    (hf : ∀ a, (f a).Valid) (as : List α) :
    ComplexRawQuotient.ofRaw (LocalODE.sum (as.map f))
      (LocalODE.sum_valid _ (by
        intro z hz
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
        exact hf a))=
    indexSum (fun a => ComplexRawQuotient.ofRaw (f a) (hf a)) as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change ComplexRawQuotient.ofRaw (f a) (hf a)+
      ComplexRawQuotient.ofRaw (LocalODE.sum (as.map f)) (LocalODE.sum_valid _ (by
        intro z hz
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
        exact hf a)) = _
    rw [ih]
    rfl

/-- A supplied finite permutation changes only the enumeration, not the value.
The executable sum and validity proofs are retained beneath exact raw equality. -/
theorem representedSum_reindex {α : Type} (f : α → ComplexRaw)
    (hf : ∀ a, (f a).Valid) {as bs : List α} (h : as.Perm bs) :
    (LocalODE.sum (as.map f)).Equiv (LocalODE.sum (bs.map f)) := by
  have hv (xs : List α) : (LocalODE.sum (xs.map f)).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    exact hf a
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := hv as) (hright := hv bs)
  rw [indexSum_raw f hf as,indexSum_raw f hf bs]
  exact indexSum_perm _ h

/-- In particular, finite CM inverse-power sums are independent of ordering. -/
theorem cmInversePowerSum_reindex (k : Nat)
    {as bs : List {u : QuadraticOrder163 // u≠QuadraticOrder163.zero}}
    (h : as.Perm bs) :
    (LocalODE.sum (as.map (fun u => LocalODE.power
      (QuadraticOrder163.complexInverse u.val u.property).val k))).Equiv
    (LocalODE.sum (bs.map (fun u => LocalODE.power
      (QuadraticOrder163.complexInverse u.val u.property).val k))) :=
  representedSum_reindex
    (fun (u : {u : QuadraticOrder163 // u≠QuadraticOrder163.zero}) =>
      LocalODE.power (QuadraticOrder163.complexInverse u.val u.property).val k)
    (fun u => LocalODE.power_valid _
      (QuadraticOrder163.complexInverse u.val u.property).property k) h

end ComputableAnalysis.ModularForms
