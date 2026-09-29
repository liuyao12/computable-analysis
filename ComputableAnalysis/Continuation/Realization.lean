import ComputableAnalysis.Continuation.Gluing
import ComputableAnalysis.Continuation.Affine

/-!
# Realizing locally coherent charts

The evaluator actually selects a chart and evaluates it at the input. Its
representation invariance is proved from local coherence, not supplied as an
extra global equality. Selection and radii remain executable data; no quotient
representative, classical choice, or domain-membership decision is used.

This is the realization step for a *supplied locally coherent selection*.
Obtaining that selection from arbitrary continuation data remains separate.
-/
namespace ComputableAnalysis.Continuation
open ComplexRaw FunctionTheory

namespace Realization
variable (D : ComplexRaw → Prop) (C : ComplexRaw → Chart)
variable (domain_congr : ∀ {a b}, a.Valid → b.Valid → a.Equiv b → (D a ↔ D b))
variable (mem : ∀ a, a.Valid → D a → (C a).map.domain a)
variable (radius : ∀ a, a.Valid → D a → QPos)
variable (inside : ∀ a ha hDa z, z.Valid → Small (sub z a) (radius a ha hDa).val → D z)
variable (coherent : ∀ a ha hDa z (hz : z.Valid),
  Small (sub z a) (radius a ha hDa).val → AgreeAt ⟨z,hz⟩ (C z).map (C a).map)

/-- The raw computation is exactly evaluation in the selected chart. -/
def map : FunctionTheory.Map where
  domain := D
  eval := fun z => (C z).map.eval z
  valid := fun z hz hDz => (C z).map.valid z hz (mem z hz hDz)
  domain_congr := domain_congr
  eval_congr := by
    intro a b ha hb hDa hDb hab
    have hba : Small (sub b a) (radius a ha hDa).val :=
      Small.congr (sub_valid ha ha) (sub_valid hb ha)
        (FunctionTheory.sub_congr hab (equiv_refl a ha))
        (Small.sub_self a ha (Rat.le_of_lt (radius a ha hDa).property))
    have habmem := ((C a).map.domain_congr ha hb hab).mp (mem a ha hDa)
    exact equiv_trans ((C a).map.valid a ha (mem a ha hDa))
      ((C a).map.valid b hb habmem) ((C b).map.valid b hb (mem b hb hDb))
      ((C a).map.eval_congr ha hb (mem a ha hDa) habmem hab)
      (equiv_symm (coherent a ha hDa b hb hba).value)

/-- The selected evaluator agrees on a whole neighborhood with one fixed
chart. This supplies the previously checked gluing theorem. -/
def localModels : LocalModels (map D C domain_congr mem radius coherent) where
  chart := C
  radius := radius
  agreement := by
    intro a ha hDa z hz hza
    have h := coherent a ha hDa z hz hza
    obtain ⟨r,hr⟩ := h
    have hm := hr z hz (Small.sub_self z hz (Rat.le_of_lt r.property))
    exact ⟨inside a ha hDa z hz hza,hm.2.1,hm.2.2⟩

/-- Exact holomorphic realization at arbitrary represented inputs. -/
def holomorphic : Holomorphic (map D C domain_congr mem radius coherent) :=
  (localModels D C domain_congr mem radius inside coherent).holomorphic

/-- A competing map with the same local germs has the same represented
values. Neither a global uniqueness field nor an identity theorem is used. -/
theorem unique (g : FunctionTheory.Map)
    (hg : ∀ a (ha : a.Valid), D a → AgreeAt ⟨a,ha⟩ g (C a).map)
    (a : ComplexRaw) (ha : a.Valid) (hDa : D a) :
    (g.eval a).Equiv ((map D C domain_congr mem radius coherent).eval a) :=
  (hg a ha hDa).value

end Realization

namespace Affine
/-- A concrete executable client of the realization construction. -/
def realized (f : Affine) : FunctionTheory.Map :=
  Realization.map (fun _ => True)
    (fun _ => ⟨f.chart,affine_holomorphic f.slope f.intercept f.slope_valid f.intercept_valid⟩)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ => True.intro)
    (fun _ _ _ => ⟨1,by decide⟩)
    (fun _ _ _ z hz _ => (f.localFunction ⟨z,hz⟩).agree_refl)

def realized_holomorphic (f : Affine) : Holomorphic f.realized :=
  Realization.holomorphic (fun _ => True)
    (fun _ => ⟨f.chart,affine_holomorphic f.slope f.intercept f.slope_valid f.intercept_valid⟩)
    (fun _ _ _ => Iff.rfl) (fun _ _ _ => True.intro)
    (fun _ _ _ => ⟨1,by decide⟩) (fun _ _ _ _ _ _ => True.intro)
    (fun _ _ _ z hz _ => (f.localFunction ⟨z,hz⟩).agree_refl)
end Affine
end ComputableAnalysis.Continuation
