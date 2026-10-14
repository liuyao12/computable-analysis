import ComputableAnalysis.RiemannHilbert.ScalarPaths
import ComputableAnalysis.RiemannHilbert.AtlasChains

/-! Whole-cell covers of actual continuous paths construct intrinsic atlas
transport. Fibers retain their changing local frames and transition cocycle;
no common frame or globally trivial bundle is required. Within-chart splitting
derives both coverage and order for arbitrary represented split parameters. -/
namespace ComputableAnalysis.RiemannHilbert
universe u
open ComplexRaw FunctionTheory UnitInterval

inductive CoveredAtlasDivision {I : Type u} {n : Nat} (a : CoefficientAtlas I n)
    {p q : Scalar} (f : ScalarPaths.Path p q) : Point → Point → Type u where
  | nil (s : Point) : CoveredAtlasDivision a f s s
  | step {s t r : Point} (chart : I) (ordered : s.value.Le t.value)
      (inside : ∀ u, (a.chart chart).domain ((ScalarPaths.subpath f s t).eval u))
      (tail : CoveredAtlasDivision a f t r) : CoveredAtlasDivision a f s r

namespace CoveredAtlasDivision
variable {I : Type u} {n : Nat} {a : CoefficientAtlas I n} {p q : Scalar}
variable {f : ScalarPaths.Path p q} {s t r : Point}

theorem ordered (d : CoveredAtlasDivision a f s t) : s.value.Le t.value := by
  induction d with
  | nil s => exact RealRaw.le_refl s.value s.valid
  | @step s t r i hst hmem tail ih => exact RealRaw.le_trans t.valid hst ih

def length : {s t : Point} → CoveredAtlasDivision a f s t → Nat
  | _, _, .nil _ => 0
  | _, _, .step _ _ _ tail => length tail+1

theorem start_mem (f : ScalarPaths.Path p q) (i : I) (s t : Point)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) :
    (a.chart i).domain (f.eval s) :=
  ((a.chart i).domain_congr ((ScalarPaths.subpath f s t).eval UnitInterval.zero) (f.eval s)
    (ScalarPaths.subpath f s t).source).1 (hmem UnitInterval.zero)

theorem end_mem (f : ScalarPaths.Path p q) (i : I) (s t : Point)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) :
    (a.chart i).domain (f.eval t) :=
  ((a.chart i).domain_congr ((ScalarPaths.subpath f s t).eval UnitInterval.one) (f.eval t)
    (ScalarPaths.subpath f s t).target).1 (hmem UnitInterval.one)

def toChain : {s t : Point} → CoveredAtlasDivision a f s t → AtlasChain a (f.eval s) (f.eval t)
  | _, _, .nil s => .nil (f.eval s)
  | s, _, .step (t := t) i _ hmem tail =>
      .step i (start_mem f i s t hmem) (end_mem f i s t hmem) (toChain tail)

def transport (d : CoveredAtlasDivision a f s t) : ValueIso (a.PointFiber (f.eval s)) (a.PointFiber (f.eval t)) :=
  AtlasChain.transport d.toChain

def reindex {s' t' : Point} (hs : s=s') (ht : t=t')
    (d : CoveredAtlasDivision a f s t) : CoveredAtlasDivision a f s' t' := by
  cases hs
  cases ht
  exact d

theorem length_reindex {s' t' : Point} (hs : s=s') (ht : t=t') (d : CoveredAtlasDivision a f s t) :
    length (reindex hs ht d) = length d := by
  cases hs
  cases ht
  rfl

def append : {s t r : Point} → CoveredAtlasDivision a f s t → CoveredAtlasDivision a f t r → CoveredAtlasDivision a f s r
  | _, _, _, .nil _, e => e
  | _, _, _, .step i hst hmem tail, e => .step i hst hmem (append tail e)

theorem length_append (d : CoveredAtlasDivision a f s t) (e : CoveredAtlasDivision a f t r) :
    length (d.append e) = length d+length e := by
  induction d with
  | nil => simp only [append, length, Nat.zero_add]
  | step i hst hmem tail ih => simp only [append, length, ih]; omega

theorem toChain_append (d : CoveredAtlasDivision a f s t) (e : CoveredAtlasDivision a f t r) :
    toChain (d.append e) = (toChain d).append (toChain e) := by
  induction d with
  | nil => rfl
  | step i hst hmem tail ih => simp only [append, toChain, AtlasChain.append, ih]

theorem transport_append (d : CoveredAtlasDivision a f s t) (e : CoveredAtlasDivision a f t r) :
    (transport (d.append e)).forward.Equiv ((transport d).forward.followedBy (transport e).forward) := by
  unfold transport
  rw [toChain_append]
  exact AtlasChain.transport_append d.toChain e.toChain

def edge (f : ScalarPaths.Path p q) (i : I) (s t : Point) (hst : s.value.Le t.value)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) : CoveredAtlasDivision a f s t :=
  .step i hst hmem (.nil t)

theorem edge_transport (f : ScalarPaths.Path p q) (i : I) (s t : Point) (hst : s.value.Le t.value)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) :
    (transport (edge f i s t hst hmem)).forward.Equiv
      (a.localTransport i (f.eval s) (f.eval t) (start_mem f i s t hmem) (end_mem f i s t hmem)).forward :=
  fun _ => Setoid.refl _

theorem first_inside (f : ScalarPaths.Path p q) (i : I) (s t v : Point)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) (u : Point) :
    (a.chart i).domain ((ScalarPaths.subpath f s (segment s t v)).eval u) :=
  ((a.chart i).domain_congr ((ScalarPaths.subpath f s (segment s t v)).eval u)
    ((ScalarPaths.subpath f s t).eval (segment UnitInterval.zero v u))
    (ScalarPaths.first_restriction f s t v u)).2 (hmem _)

theorem second_inside (f : ScalarPaths.Path p q) (i : I) (s t v : Point)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) (u : Point) :
    (a.chart i).domain ((ScalarPaths.subpath f (segment s t v) t).eval u) :=
  ((a.chart i).domain_congr ((ScalarPaths.subpath f (segment s t v) t).eval u)
    ((ScalarPaths.subpath f s t).eval (segment v UnitInterval.one u))
    (ScalarPaths.second_restriction f s t v u)).2 (hmem _)

def split (f : ScalarPaths.Path p q) (i : I) (s t : Point) (hst : s.value.Le t.value)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) (v : Point)
    (tail : CoveredAtlasDivision a f t r) : CoveredAtlasDivision a f s r :=
  .step i (le_segment s t v hst) (first_inside f i s t v hmem)
    (.step i (segment_le s t v hst) (second_inside f i s t v hmem) tail)

theorem split_transport (f : ScalarPaths.Path p q) (i : I) (s t : Point) (hst : s.value.Le t.value)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) (v : Point)
    (tail : CoveredAtlasDivision a f t r) :
    (transport (split f i s t hst hmem v tail)).forward.Equiv
      (transport (.step i hst hmem tail)).forward := by
  intro x
  exact (transport tail).forward.congr (a.localTransport_compose i
    (f.eval s) (f.eval (segment s t v)) (f.eval t)
    (start_mem f i s t hmem) (end_mem f i s (segment s t v) (first_inside f i s t v hmem))
    (end_mem f i s t hmem) x)

theorem split_length (f : ScalarPaths.Path p q) (i : I) (s t : Point) (hst : s.value.Le t.value)
    (hmem : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s t).eval u)) (v : Point)
    (tail : CoveredAtlasDivision a f t r) : length (split f i s t hst hmem v tail) = length tail+2 := by
  simp only [split, length]

def bisect (v : Point) : {s t : Point} → CoveredAtlasDivision a f s t → CoveredAtlasDivision a f s t
  | _, _, .nil s => .nil s
  | s, _, .step (t := t) i hst hmem tail => split f i s t hst hmem v (bisect v tail)

theorem bisect_length (v : Point) (d : CoveredAtlasDivision a f s t) : length (bisect v d) = 2*length d := by
  induction d with
  | nil => rfl
  | step i hst hmem tail ih => simp only [bisect, split_length, length, ih]; omega

theorem bisect_transport (v : Point) (d : CoveredAtlasDivision a f s t) :
    (transport (bisect v d)).forward.Equiv (transport d).forward := by
  induction d with
  | nil => exact ValueMap.equiv_refl _
  | @step s t r i hst hmem tail ih =>
    exact ValueMap.equiv_trans (split_transport f i s t hst hmem v (bisect v tail))
      (ValueMap.followedBy_congr (ValueMap.equiv_refl _) ih)

def iterate (v : Point) (d : CoveredAtlasDivision a f s t) : Nat → CoveredAtlasDivision a f s t
  | 0 => d
  | k+1 => bisect v (iterate v d k)

theorem iterate_length (v : Point) (d : CoveredAtlasDivision a f s t) (k : Nat) :
    length (iterate v d k) = 2^k*length d := by
  induction k with
  | zero => simp only [iterate, Nat.pow_zero, Nat.one_mul]
  | succ k ih =>
    simp only [iterate, bisect_length, ih, Nat.pow_succ]
    rw [Nat.mul_comm (2^k) 2, Nat.mul_assoc]

theorem iterate_transport (v : Point) (d : CoveredAtlasDivision a f s t) (k : Nat) :
    (transport (iterate v d k)).forward.Equiv (transport d).forward := by
  induction k with
  | zero => exact ValueMap.equiv_refl _
  | succ k ih => exact ValueMap.equiv_trans (bisect_transport v (iterate v d k)) ih

theorem iterate_inverse_transport (v : Point) (d : CoveredAtlasDivision a f s t) (k : Nat) :
    (transport (iterate v d k)).backward.Equiv (transport d).backward :=
  ValueIso.inverse_congr _ _ (iterate_transport v d k)

theorem iterate_independent (v w : Point) (d : CoveredAtlasDivision a f s t) (k l : Nat) :
    (transport (iterate v d k)).forward.Equiv (transport (iterate w d l)).forward :=
  ValueMap.equiv_trans (iterate_transport v d k) (ValueMap.equiv_symm (iterate_transport w d l))

theorem inverse_recovers (d : CoveredAtlasDivision a f s t) (x : a.PointFiber (f.eval s)) :
    (transport d).backward.eval ((transport d).forward.eval x) ≈ x := (transport d).backward_forward x

theorem transport_add (d : CoveredAtlasDivision a f s t) (x y : a.PointFiber (f.eval s)) :
    (transport d).forward.eval (AtlasFiber.add x y) ≈
      AtlasFiber.add ((transport d).forward.eval x) ((transport d).forward.eval y) :=
  AtlasChain.transport_add d.toChain x y

theorem transport_scale (d : CoveredAtlasDivision a f s t) (c : Scalar) (x : a.PointFiber (f.eval s)) :
    (transport d).forward.eval (AtlasFiber.scale c x) ≈ AtlasFiber.scale c ((transport d).forward.eval x) :=
  AtlasChain.transport_scale d.toChain c x

end CoveredAtlasDivision
end ComputableAnalysis.RiemannHilbert
