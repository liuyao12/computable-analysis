import ComputableAnalysis.ComplexMultiplication

/-!
# Continuity of represented values

Continuity uses exact arithmetic and order on valid represented numbers.
At a point, a positive rational tolerance is sent to a positive rational
radius. On a domain, these pointwise radii may depend on the base point.
No common output stage, uniform domain modulus, or completed number system
is part of the law. Radius functions preserve executable implementations;
a function type alone is not a computability certificate.
-/
namespace ComputableAnalysis.RealFunctionTheory

/-- Exact represented bound `-r ≤ x ≤ r`, using `RealRaw.Le`. -/
def Small (x : RealRaw) (r : Rat) : Prop :=
  (RealRaw.ofRat (-r)).Le x ∧ x.Le (RealRaw.ofRat r)

theorem Small.congr {x y : RealRaw} {r : Rat}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) (h : Small x r) :
    Small y r := by
  exact ⟨RealRaw.le_trans hx h.1 (RealRaw.le_of_equiv hx hy hxy),
    RealRaw.le_trans hx (RealRaw.le_of_equiv hy hx (RealRaw.equiv_symm hxy)) h.2⟩

theorem Small.sub_self (x : RealRaw) (hx : x.Valid) {r : Rat} (hr : 0 ≤ r) :
    Small (x - x) r := by
  constructor
  · intro n m
    have h := RealRaw.interval_order_of_valid x hx m
    change -r ≤ (x.compute m).hi - (x.compute m).lo
    grind
  · intro n m
    have h := RealRaw.interval_order_of_valid x hx n
    change (x.compute n).lo - (x.compute n).hi ≤ r
    grind

/-- Continuity relative to the domain at one valid represented point.
The public estimate is a bound on values, not on finite output boxes. -/
structure ContinuousAt (domain : RealRaw → Prop) (g : RealRaw → RealRaw) (a : RealRaw) where
  point_valid : a.Valid
  point_mem : domain a
  delta : QPos → QPos
  estimate : ∀ (eps : QPos) y, y.Valid → domain y →
    Small (y - a) (delta eps).val → Small ((g y) - (g a)) eps.val

/-- Continuity at every valid point of the domain, with point-dependent radii.
This is not uniform continuity on the whole domain. -/
structure ContinuousOn (domain : RealRaw → Prop) (g : RealRaw → RealRaw) where
  delta : ∀ a, a.Valid → domain a → QPos → QPos
  estimate : ∀ a ha hfa (eps : QPos) y, y.Valid → domain y →
    Small (y - a) (delta a ha hfa eps).val → Small ((g y) - (g a)) eps.val

/-- Extract the pointwise witness without changing its radius. -/
def ContinuousOn.atPoint {D : RealRaw → Prop} {g : RealRaw → RealRaw}
    (h : ContinuousOn D g) (a : RealRaw) (ha : a.Valid) (hDa : D a) :
    ContinuousAt D g a where
  point_valid := ha
  point_mem := hDa
  delta := h.delta a ha hDa
  estimate := h.estimate a ha hDa

/-- Assemble supplied pointwise computations; no uniform radius is selected. -/
def ContinuousOn.ofAtPoint {D : RealRaw → Prop} {g : RealRaw → RealRaw}
    (h : ∀ a, a.Valid → D a → ContinuousAt D g a) : ContinuousOn D g where
  delta := fun a ha hDa => (h a ha hDa).delta
  estimate := fun a ha hDa => (h a ha hDa).estimate

/-- Change the input name while preserving the same radius computation. -/
def ContinuousAt.congrPoint {D : RealRaw → Prop} {g : RealRaw → RealRaw}
    {a b : RealRaw} (h : ContinuousAt D g a) (hb : b.Valid) (hab : a.Equiv b)
    (domain_congr : ∀ {x y}, x.Valid → y.Valid → x.Equiv y → (D x ↔ D y))
    (valid : ∀ x, x.Valid → D x → (g x).Valid)
    (eval_congr : ∀ {x y}, x.Valid → y.Valid → D x → D y →
      x.Equiv y → (g x).Equiv (g y)) : ContinuousAt D g b where
  point_valid := hb
  point_mem := (domain_congr h.point_valid hb hab).mp h.point_mem
  delta := h.delta
  estimate := by
    intro eps y hy hDy hyb
    have hDb := (domain_congr h.point_valid hb hab).mp h.point_mem
    have input_equiv := RealRaw.sub_equiv hy hy h.point_valid hb (RealRaw.equiv_refl y hy) hab
    have hya := Small.congr (RealRaw.sub_valid hy hb)
      (RealRaw.sub_valid hy h.point_valid) (RealRaw.equiv_symm input_equiv) hyb
    have output_equiv := RealRaw.sub_equiv (valid y hy hDy) (valid y hy hDy) (valid a h.point_valid h.point_mem) (valid b hb hDb) (RealRaw.equiv_refl (g y) (valid y hy hDy)) (eval_congr h.point_valid hb h.point_mem hDb hab)
    exact Small.congr (RealRaw.sub_valid (valid y hy hDy) (valid a h.point_valid h.point_mem))
      (RealRaw.sub_valid (valid y hy hDy) (valid b hb hDb)) output_equiv (h.estimate eps y hy hDy hya)

/-- Equivalent evaluators have the same continuity law and can reuse radii. -/
def ContinuousAt.congrEval {D : RealRaw → Prop} {g k : RealRaw → RealRaw}
    {a : RealRaw} (h : ContinuousAt D g a)
    (vg : ∀ x, x.Valid → D x → (g x).Valid)
    (vk : ∀ x, x.Valid → D x → (k x).Valid)
    (agree : ∀ x, x.Valid → D x → (g x).Equiv (k x)) : ContinuousAt D k a where
  point_valid := h.point_valid
  point_mem := h.point_mem
  delta := h.delta
  estimate := by
    intro eps y hy hDy hya
    exact Small.congr (RealRaw.sub_valid (vg y hy hDy) (vg a h.point_valid h.point_mem))
      (RealRaw.sub_valid (vk y hy hDy) (vk a h.point_valid h.point_mem))
      (RealRaw.sub_equiv (vg y hy hDy) (vk y hy hDy) (vg a h.point_valid h.point_mem) (vk a h.point_valid h.point_mem) (agree y hy hDy) (agree a h.point_valid h.point_mem))
      (h.estimate eps y hy hDy hya)

def ContinuousOn.congrEval {D : RealRaw → Prop} {g k : RealRaw → RealRaw}
    (h : ContinuousOn D g)
    (vg : ∀ x, x.Valid → D x → (g x).Valid)
    (vk : ∀ x, x.Valid → D x → (k x).Valid)
    (agree : ∀ x, x.Valid → D x → (g x).Equiv (k x)) : ContinuousOn D k :=
  .ofAtPoint fun a ha hDa => (h.atPoint a ha hDa).congrEval vg vk agree

/-- Identity on any domain, with the literal radius `delta = eps`. -/
def continuousOn_identity (D : RealRaw → Prop) : ContinuousOn D (fun x => x) where
  delta := fun _ _ _ eps => eps
  estimate := fun _ _ _ _ _ _ _ h => h

/-- Every valid represented constant is continuous on any domain. -/
def continuousOn_constant (D : RealRaw → Prop) (c : RealRaw) (hc : c.Valid) :
    ContinuousOn D (fun _ => c) where
  delta := fun _ _ _ eps => eps
  estimate := fun _ _ _ eps _ _ _ _ => Small.sub_self c hc (Rat.le_of_lt eps.property)

end ComputableAnalysis.RealFunctionTheory

namespace ComputableAnalysis.FunctionTheory
open ComplexRaw

/-- Exact closed coordinate bound, not a bound on an arbitrarily early box.
For valid inputs this says both represented coordinates lie in `[-r,r]`. -/
def Small (z : ComplexRaw) (r : Rat) : Prop :=
  (RealRaw.ofRat (-r)).Le z.realPart ∧ z.realPart.Le (RealRaw.ofRat r) ∧
  (RealRaw.ofRat (-r)).Le z.imagPart ∧ z.imagPart.Le (RealRaw.ofRat r)

theorem Small.congr {z w : ComplexRaw} {r : Rat}
    (hz : z.Valid) (hw : w.Valid) (hzw : z.Equiv w) (h : Small z r) :
    Small w r := by
  have hr := ComplexRaw.realPart_equiv hzw
  have hi := ComplexRaw.imagPart_equiv hzw
  have hzr := realPart_valid hz
  have hwr := realPart_valid hw
  have hzi := imagPart_valid hz
  have hwi := imagPart_valid hw
  exact ⟨RealRaw.le_trans hzr h.1 (RealRaw.le_of_equiv hzr hwr hr),
    RealRaw.le_trans hzr (RealRaw.le_of_equiv hwr hzr (RealRaw.equiv_symm hr)) h.2.1,
    RealRaw.le_trans hzi h.2.2.1 (RealRaw.le_of_equiv hzi hwi hi),
    RealRaw.le_trans hzi (RealRaw.le_of_equiv hwi hzi (RealRaw.equiv_symm hi)) h.2.2.2⟩

theorem Small.zero {r : Rat} (hr : 0 ≤ r) : Small ComplexRaw.zero r := by
  constructor
  · intro n m; change -r ≤ 0; grind
  constructor
  · intro n m; exact hr
  constructor
  · intro n m; change -r ≤ 0; grind
  · intro n m; exact hr

theorem Small.mono {z : ComplexRaw} {r s : Rat}
    (h : Small z r) (hrs : r ≤ s) : Small z s := by
  rcases h with ⟨h1,h2,h3,h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m; exact Rat.le_trans (Rat.neg_le_neg hrs) (h1 n m)
  · intro n m; exact Rat.le_trans (h2 n m) hrs
  · intro n m; exact Rat.le_trans (Rat.neg_le_neg hrs) (h3 n m)
  · intro n m; exact Rat.le_trans (h4 n m) hrs

/-- Continuity relative to the domain at one valid represented point.
The public estimate is a bound on values, not on finite output boxes. -/
structure ContinuousAt (domain : ComplexRaw → Prop) (g : ComplexRaw → ComplexRaw) (a : ComplexRaw) where
  point_valid : a.Valid
  point_mem : domain a
  delta : QPos → QPos
  estimate : ∀ (eps : QPos) y, y.Valid → domain y →
    Small (ComplexRaw.sub y a) (delta eps).val → Small (ComplexRaw.sub (g y) (g a)) eps.val

/-- Continuity at every valid point of the domain, with point-dependent radii.
This is not uniform continuity on the whole domain. -/
structure ContinuousOn (domain : ComplexRaw → Prop) (g : ComplexRaw → ComplexRaw) where
  delta : ∀ a, a.Valid → domain a → QPos → QPos
  estimate : ∀ a ha hfa (eps : QPos) y, y.Valid → domain y →
    Small (ComplexRaw.sub y a) (delta a ha hfa eps).val → Small (ComplexRaw.sub (g y) (g a)) eps.val

/-- Extract the pointwise witness without changing its radius. -/
def ContinuousOn.atPoint {D : ComplexRaw → Prop} {g : ComplexRaw → ComplexRaw}
    (h : ContinuousOn D g) (a : ComplexRaw) (ha : a.Valid) (hDa : D a) :
    ContinuousAt D g a where
  point_valid := ha
  point_mem := hDa
  delta := h.delta a ha hDa
  estimate := h.estimate a ha hDa

/-- Assemble supplied pointwise computations; no uniform radius is selected. -/
def ContinuousOn.ofAtPoint {D : ComplexRaw → Prop} {g : ComplexRaw → ComplexRaw}
    (h : ∀ a, a.Valid → D a → ContinuousAt D g a) : ContinuousOn D g where
  delta := fun a ha hDa => (h a ha hDa).delta
  estimate := fun a ha hDa => (h a ha hDa).estimate

/-- Change the input name while preserving the same radius computation. -/
def ContinuousAt.congrPoint {D : ComplexRaw → Prop} {g : ComplexRaw → ComplexRaw}
    {a b : ComplexRaw} (h : ContinuousAt D g a) (hb : b.Valid) (hab : a.Equiv b)
    (domain_congr : ∀ {x y}, x.Valid → y.Valid → x.Equiv y → (D x ↔ D y))
    (valid : ∀ x, x.Valid → D x → (g x).Valid)
    (eval_congr : ∀ {x y}, x.Valid → y.Valid → D x → D y →
      x.Equiv y → (g x).Equiv (g y)) : ContinuousAt D g b where
  point_valid := hb
  point_mem := (domain_congr h.point_valid hb hab).mp h.point_mem
  delta := h.delta
  estimate := by
    intro eps y hy hDy hyb
    have hDb := (domain_congr h.point_valid hb hab).mp h.point_mem
    have input_equiv := ComplexRaw.add_equiv (ComplexRaw.equiv_refl y hy) (ComplexRaw.neg_equiv hab)
    have hya := Small.congr (ComplexRaw.sub_valid hy hb)
      (ComplexRaw.sub_valid hy h.point_valid) (ComplexRaw.equiv_symm input_equiv) hyb
    have output_equiv := ComplexRaw.add_equiv (ComplexRaw.equiv_refl (g y) (valid y hy hDy)) (ComplexRaw.neg_equiv (eval_congr h.point_valid hb h.point_mem hDb hab))
    exact Small.congr (ComplexRaw.sub_valid (valid y hy hDy) (valid a h.point_valid h.point_mem))
      (ComplexRaw.sub_valid (valid y hy hDy) (valid b hb hDb)) output_equiv (h.estimate eps y hy hDy hya)

/-- Equivalent evaluators have the same continuity law and can reuse radii. -/
def ContinuousAt.congrEval {D : ComplexRaw → Prop} {g k : ComplexRaw → ComplexRaw}
    {a : ComplexRaw} (h : ContinuousAt D g a)
    (vg : ∀ x, x.Valid → D x → (g x).Valid)
    (vk : ∀ x, x.Valid → D x → (k x).Valid)
    (agree : ∀ x, x.Valid → D x → (g x).Equiv (k x)) : ContinuousAt D k a where
  point_valid := h.point_valid
  point_mem := h.point_mem
  delta := h.delta
  estimate := by
    intro eps y hy hDy hya
    exact Small.congr (ComplexRaw.sub_valid (vg y hy hDy) (vg a h.point_valid h.point_mem))
      (ComplexRaw.sub_valid (vk y hy hDy) (vk a h.point_valid h.point_mem))
      (ComplexRaw.add_equiv (agree y hy hDy) (ComplexRaw.neg_equiv (agree a h.point_valid h.point_mem)))
      (h.estimate eps y hy hDy hya)

def ContinuousOn.congrEval {D : ComplexRaw → Prop} {g k : ComplexRaw → ComplexRaw}
    (h : ContinuousOn D g)
    (vg : ∀ x, x.Valid → D x → (g x).Valid)
    (vk : ∀ x, x.Valid → D x → (k x).Valid)
    (agree : ∀ x, x.Valid → D x → (g x).Equiv (k x)) : ContinuousOn D k :=
  .ofAtPoint fun a ha hDa => (h.atPoint a ha hDa).congrEval vg vk agree

/-- Identity on any domain, with the literal radius `delta = eps`. -/
def continuousOn_identity (D : ComplexRaw → Prop) : ContinuousOn D (fun x => x) where
  delta := fun _ _ _ eps => eps
  estimate := fun _ _ _ _ _ _ _ h => h

end ComputableAnalysis.FunctionTheory
