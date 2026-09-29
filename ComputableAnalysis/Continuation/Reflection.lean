import ComputableAnalysis.Continuation.PolynomialIdentity
import ComputableAnalysis.Continuation.Germ

/-!
# Reflected holomorphic charts

Conjugating the input and output preserves holomorphicity, with the original
rational radii. This supplies the reflected *open* chart in Schwarz reflection.
It does not prove holomorphic gluing across the real boundary from continuity
and real boundary values alone; that seam theorem remains a separate task.
-/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw Continuation

theorem Small.conj {z : ComplexRaw} {r : Rat} (h : Small z r) :
    Small (ComplexRaw.conj z) r := by
  refine ⟨h.1,h.2.1,?_,?_⟩ <;> intro n m
  · have h' := h.2.2.2 m n
    change (z.compute m).lo.im ≤ r at h'
    change -r ≤ -(z.compute m).lo.im
    grind
  · have h' := h.2.2.1 m n
    change -r ≤ (z.compute n).hi.im at h'
    change -(z.compute n).hi.im ≤ r
    grind

private theorem conjugate_sub (a b : ComplexRaw) (ha : a.Valid) (hb : b.Valid) :
    (conj (sub a b)).Equiv (sub (conj a) (conj b)) := by
  let v : Nat → ComplexRaw := fun n => if n=0 then a else b
  have hv : ∀ n, (v n).Valid := by intro n; dsimp [v]; split <;> assumption
  exact PolynomialExpr.identity (.conj (.add (.var 0) (.neg (.var 1))))
    (.add (.conj (.var 0)) (.neg (.conj (.var 1)))) v hv (by
      intro p; simp [PolynomialExpr.rational,QComplex.conj_add,QComplex.conj_neg])

private theorem reflected_small {a b : ComplexRaw} {r : Rat}
    (ha : a.Valid) (hb : b.Valid) (h : Small (sub a b) r) :
    Small (sub (conj a) (conj b)) r :=
  Small.congr (conj_valid _ (sub_valid ha hb))
    (sub_valid (conj_valid a ha) (conj_valid b hb)) (conjugate_sub a b ha hb) h.conj

/-- The reflected chart, with its reflected domain. -/
def Map.reflect (f : Map) : Map where
  domain := fun z => f.domain (conj z)
  eval := fun z => conj (f.eval (conj z))
  valid := fun z hz hfz => conj_valid _ (f.valid _ (conj_valid z hz) hfz)
  domain_congr := fun ha hb hab => f.domain_congr (conj_valid _ ha) (conj_valid _ hb) (conj_equiv hab)
  eval_congr := fun ha hb hfa hfb hab =>
    conj_equiv (f.eval_congr (conj_valid _ ha) (conj_valid _ hb) hfa hfb (conj_equiv hab))

private theorem reflect_remainder (f : Map) (a d z : ComplexRaw)
    (ha : a.Valid) (hd : d.Valid) (hz : z.Valid)
    (hfa : f.domain (conj a)) (hfz : f.domain (conj z)) :
    (conj (remainder f (conj a) d (conj z))).Equiv
      (remainder f.reflect a (conj d) z) := by
  let v : Nat → ComplexRaw := fun n =>
    if n=0 then f.eval (conj z) else if n=1 then f.eval (conj a)
    else if n=2 then d else if n=3 then z else a
  have hv : ∀ n, (v n).Valid := by
    intro n; dsimp [v]; split
    · exact f.valid _ (conj_valid z hz) hfz
    · split
      · exact f.valid _ (conj_valid a ha) hfa
      · split
        · exact hd
        · split <;> assumption
  let lhs : PolynomialExpr := .conj (.add (.add (.var 0) (.neg (.var 1)))
    (.neg (.mul (.var 2) (.add (.conj (.var 3)) (.neg (.conj (.var 4)))))))
  let rhs : PolynomialExpr := .add (.add (.conj (.var 0)) (.neg (.conj (.var 1))))
    (.neg (.mul (.conj (.var 2)) (.add (.var 3) (.neg (.var 4)))))
  exact PolynomialExpr.identity lhs rhs v hv (by
    intro p
    simp only [lhs,rhs,PolynomialExpr.rational,QComplex.conj_add,QComplex.conj_neg,
      QComplex.conj_mul]
    simp [QComplex.conj])

/-- Quantitative complex differentiability of the reflected chart. -/
def HasDerivativeAt.reflect {f : Map} {a d : ComplexRaw} (ha : a.Valid)
    (h : HasDerivativeAt f (conj a) d) : HasDerivativeAt f.reflect a (conj d) where
  point_valid := ha
  point_mem := h.point_mem
  derivative_valid := conj_valid d h.derivative_valid
  delta := h.delta
  estimate := by
    intro eps H z hz hfz hH hza
    have hc := h.estimate eps H (conj z) (conj_valid z hz) hfz hH (reflected_small hz ha hza)
    exact Small.congr (conj_valid _ (remainder_valid f h.point_valid h.derivative_valid
      (conj_valid z hz) h.point_mem hfz))
      (remainder_valid f.reflect ha (conj_valid d h.derivative_valid) hz h.point_mem hfz)
      (reflect_remainder f a d z ha h.derivative_valid hz h.point_mem hfz) hc.conj

/-- Reflection in both variables preserves holomorphicity at arbitrary
represented inputs. This includes derivative continuity with unchanged radii. -/
def Holomorphic.reflect {f : Map} (h : Holomorphic f) : Holomorphic f.reflect where
  openDomain := {
    radius := fun a ha hfa => h.openDomain.radius (conj a) (conj_valid a ha) hfa
    inside := fun a ha hfa z hz hza =>
      h.openDomain.inside (conj a) (conj_valid a ha) hfa (conj z) (conj_valid z hz)
        (reflected_small hz ha hza) }
  derivative := fun a => conj (h.derivative (conj a))
  atPoint := fun a ha hfa => (h.atPoint (conj a) (conj_valid a ha) hfa).reflect ha
  derivative_congr := fun ha hb hfa hfb hab =>
    conj_equiv (h.derivative_congr (conj_valid _ ha) (conj_valid _ hb) hfa hfb (conj_equiv hab))
  continuousDerivative := {
    delta := fun a ha hfa eps => h.continuousDerivative.delta (conj a) (conj_valid a ha) hfa eps
    estimate := by
      intro a ha hfa eps z hz hfz hza
      exact reflected_small (h.atPoint (conj z) (conj_valid z hz) hfz).derivative_valid
        (h.atPoint (conj a) (conj_valid a ha) hfa).derivative_valid
        (h.continuousDerivative.estimate (conj a) (conj_valid a ha) hfa eps
          (conj z) (conj_valid z hz) hfz (reflected_small hz ha hza)) }
end ComputableAnalysis.FunctionTheory

namespace ComputableAnalysis.Continuation
open ComplexRaw FunctionTheory

/-- Reflection also preserves the open-overlap evidence used in continuation. -/
theorem AgreeAt.reflect {a : Point} {f g : FunctionTheory.Map}
    (h : AgreeAt a f g) :
    AgreeAt ⟨conj a.val,conj_valid a.val a.property⟩ f.reflect g.reflect := by
  have hc := h.congrPoint (b := ⟨conj (conj a.val),conj_valid _ (conj_valid _ a.property)⟩)
    (equiv_symm (conj_conj_equiv a.val a.property))
  obtain ⟨r,hr⟩ := hc
  refine ⟨r,fun z hz hza => ?_⟩
  have hzc := FunctionTheory.reflected_small hz (conj_valid a.val a.property) hza
  obtain ⟨hf,hg,he⟩ := hr (conj z) (conj_valid z hz) hzc
  exact ⟨hf,hg,conj_equiv he⟩
end ComputableAnalysis.Continuation
