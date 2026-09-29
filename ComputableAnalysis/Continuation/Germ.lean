import ComputableAnalysis.Continuation.Neighborhood

/-!
# Holomorphic germs with represented base points

Representatives are actual holomorphic maps on open neighborhoods. Equality
is agreement on a positive-radius neighborhood, never equality at one point.
We retain representatives and a setoid; no completion or choice of quotient
representatives enters an evaluator.
-/
namespace ComputableAnalysis.Continuation
open FunctionTheory ComplexRaw

abbrev Point := {z : ComplexRaw // z.Valid}

structure LocalFunction (a : Point) where
  map : FunctionTheory.Map
  holomorphic : Holomorphic map
  mem : map.domain a.val

/-- A neighborhood witness includes the domains of both local functions. -/
def AgreeAt (a : Point) (f g : FunctionTheory.Map) : Prop :=
  ∃ r : QPos, ∀ z, z.Valid → Small (sub z a.val) r.val →
    f.domain z ∧ g.domain z ∧ (f.eval z).Equiv (g.eval z)

theorem AgreeAt.symm {a : Point} {f g : FunctionTheory.Map}
    (h : AgreeAt a f g) : AgreeAt a g f := by
  obtain ⟨r,hr⟩ := h
  refine ⟨r, fun z hz hza => ?_⟩
  obtain ⟨hf,hg,he⟩ := hr z hz hza
  exact ⟨hg,hf,equiv_symm he⟩

theorem AgreeAt.trans {a : Point} {f g h : FunctionTheory.Map}
    (hfg : AgreeAt a f g) (hgh : AgreeAt a g h) : AgreeAt a f h := by
  obtain ⟨r,hr⟩ := hfg
  obtain ⟨s,hs⟩ := hgh
  let t : QPos := ⟨min r.val s.val, by have := r.property; have := s.property; grind⟩
  refine ⟨t, fun z hz hza => ?_⟩
  have hzr := hza.mono (show t.val ≤ r.val by dsimp [t]; grind)
  have hzs := hza.mono (show t.val ≤ s.val by dsimp [t]; grind)
  obtain ⟨hf,hg,he⟩ := hr z hz hzr
  obtain ⟨_,hh,hj⟩ := hs z hz hzs
  exact ⟨hf,hh,equiv_trans (f.valid z hz hf) (g.valid z hz hg) (h.valid z hz hh) he hj⟩

theorem AgreeAt.value {a : Point} {f g : FunctionTheory.Map}
    (h : AgreeAt a f g) : (f.eval a.val).Equiv (g.eval a.val) := by
  obtain ⟨r,hr⟩ := h
  exact (hr a.val a.property (Small.sub_self _ a.property (Rat.le_of_lt r.property))).2.2

theorem AgreeAt.congrPoint {a b : Point} {f g : FunctionTheory.Map}
    (hab : a.val.Equiv b.val) (h : AgreeAt a f g) : AgreeAt b f g := by
  obtain ⟨r,hr⟩ := h
  refine ⟨r, fun z hz hzb => hr z hz ?_⟩
  exact Small.congr (sub_valid hz b.property) (sub_valid hz a.property)
    (FunctionTheory.sub_congr (equiv_refl z hz) (equiv_symm hab)) hzb

/-- Equality of germs is itself local: a witness on a radius `r` also works
near any point within `r/2`, using a further radius `r/2`. -/
theorem agreeAt_nearby {a b : Point} {f g : FunctionTheory.Map} (r : QPos)
    (h : ∀ z, z.Valid → Small (sub z a.val) r.val →
      f.domain z ∧ g.domain z ∧ (f.eval z).Equiv (g.eval z))
    (hb : Small (sub b.val a.val) (r.val/2)) : AgreeAt b f g := by
  let half : QPos := ⟨r.val/2, by have := r.property; grind⟩
  refine ⟨half, fun z hz hzb => h z hz ?_⟩
  exact (Small.sub_triangle hz b.property a.property hzb hb).mono (by dsimp [half]; grind)

namespace LocalFunction

theorem agree_refl {a : Point} (f : LocalFunction a) : AgreeAt a f.map f.map := by
  let o := f.holomorphic.openDomain
  refine ⟨o.radius a.val a.property f.mem, fun z hz hza => ?_⟩
  have hmem := o.inside a.val a.property f.mem z hz hza
  exact ⟨hmem,hmem,equiv_refl _ (f.map.valid z hz hmem)⟩

instance {a : Point} : Setoid (LocalFunction a) where
  r f g := AgreeAt a f.map g.map
  iseqv := ⟨agree_refl, AgreeAt.symm, AgreeAt.trans⟩

def value {a : Point} (f : LocalFunction a) : ComplexRaw := f.map.eval a.val

theorem value_valid {a : Point} (f : LocalFunction a) : f.value.Valid :=
  f.map.valid a.val a.property f.mem

theorem value_congr {a : Point} {f g : LocalFunction a} (h : f ≈ g) :
    f.value.Equiv g.value := AgreeAt.value h

def rebase {a b : Point} (f : LocalFunction a) (hb : f.map.domain b.val) :
    LocalFunction b := ⟨f.map,f.holomorphic,hb⟩

def congrPoint {a b : Point} (hab : a.val.Equiv b.val) (f : LocalFunction a) :
    LocalFunction b :=
  f.rebase ((f.map.domain_congr a.property b.property hab).mp f.mem)

theorem congrPoint_value {a b : Point} (hab : a.val.Equiv b.val) (f : LocalFunction a) :
    f.value.Equiv (f.congrPoint hab).value :=
  f.map.eval_congr a.property b.property f.mem
    ((f.map.domain_congr a.property b.property hab).mp f.mem) hab

end LocalFunction
end ComputableAnalysis.Continuation
