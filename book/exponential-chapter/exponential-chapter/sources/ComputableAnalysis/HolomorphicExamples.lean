import ComputableAnalysis.Holomorphic

/-! Concrete witnesses for holomorphicity at arbitrary represented inputs.
All polynomial identities below are lifted from finite rational arithmetic by
box containment; no abstract completion or formal-jet assumption is used. -/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw

private def Mem (p : QComplex) (B : QBox) : Prop := B.lo ≤ p ∧ p ≤ B.hi

private theorem neg_mem {p : QComplex} {B : QBox} (h : Mem p B) :
    Mem (QComplex.neg p) (QBox.neg B) := by
  rcases h with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
  exact ⟨⟨Rat.neg_le_neg h3, Rat.neg_le_neg h4⟩,
    ⟨Rat.neg_le_neg h1, Rat.neg_le_neg h2⟩⟩

private inductive Expr where
  | var : Nat → Expr
  | zero : Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr

private def Expr.raw (v : Nat → ComplexRaw) : Expr → ComplexRaw
  | .var n => v n
  | .zero => ComplexRaw.zero
  | .add a b => ComplexRaw.add (a.raw v) (b.raw v)
  | .neg a => ComplexRaw.neg (a.raw v)
  | .mul a b => ComplexRaw.mul (a.raw v) (b.raw v)

private def Expr.rational (v : Nat → QComplex) : Expr → QComplex
  | .var n => v n
  | .zero => QComplex.zero
  | .add a b => QComplex.add (a.rational v) (b.rational v)
  | .neg a => QComplex.neg (a.rational v)
  | .mul a b => QComplex.mul (a.rational v) (b.rational v)

private theorem Expr.contains (e : Expr) (v : Nat → ComplexRaw)
    (p : Nat → QComplex) (n : Nat) (h : ∀ i, Mem (p i) ((v i).compute n)) :
    Mem (e.rational p) ((e.raw v).compute n) := by
  induction e with
  | var i => exact h i
  | zero => exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩
  | add a b ha hb => exact QBox.add_contains ha.1 ha.2 hb.1 hb.2
  | neg a ha => exact neg_mem ha
  | mul a b ha hb => exact QBox.mul_contains ha.1 ha.2 hb.1 hb.2

/-- A finite polynomial identity remains exact for independently boxed inputs. -/
private theorem Expr.identity (e g : Expr) (v : Nat → ComplexRaw)
    (hv : ∀ i, (v i).Valid) (he : ∀ p, e.rational p = g.rational p) :
    (e.raw v).Equiv (g.raw v) := by
  intro n
  let p := fun i => ((v i).compute n).center
  have hp : ∀ i, Mem (p i) ((v i).compute n) :=
    fun i => QBox.center_mem (valid_ordered (hv i) n)
  have hleft := e.contains v p n hp
  have hright := g.contains v p n hp
  rw [he p] at hleft
  apply (compareAt_overlap_iff _ _ n n).mpr
  exact ⟨QComplex.le_trans hleft.1 hright.2, QComplex.le_trans hright.1 hleft.2⟩

/-- An affine map with arbitrary valid represented complex coefficients. -/
def affine (c b : ComplexRaw) (hc : c.Valid) (hb : b.Valid) : Map where
  domain := fun _ => True
  eval := fun z => add (mul c z) b
  valid := fun _ hz _ => add_valid (mul_valid hc hz) hb
  domain_congr := fun _ _ _ => Iff.rfl
  eval_congr := fun hz hw _ _ hzw =>
    add_equiv (mul_equiv hc hc hz hw (equiv_refl c hc) hzw) (equiv_refl b hb)

private def entireOpen (f : Map) (hf : ∀ z, f.domain z) : OpenDomain f where
  radius := fun _ _ _ => ⟨1, by decide⟩
  inside := fun _ _ _ z _ _ => hf z

/-- The affine remainder is zero as a value, despite interval dependency loss. -/
theorem affine_remainder (c b a z : ComplexRaw)
    (hc : c.Valid) (hb : b.Valid) (ha : a.Valid) (hz : z.Valid) :
    (remainder (affine c b hc hb) a c z).Equiv ComplexRaw.zero := by
  let v : Nat → ComplexRaw := fun n => if n = 0 then c else if n = 1 then b else if n = 2 then a else z
  have hv : ∀ n, (v n).Valid := by intro n; dsimp [v]; split <;> first | assumption | (split <;> first | assumption | (split <;> assumption))
  let C := Expr.var 0
  let B := Expr.var 1
  let A := Expr.var 2
  let Z := Expr.var 3
  let E := Expr.add
    (.add (.add (.mul C Z) B) (.neg (.add (.mul C A) B)))
    (.neg (.mul C (.add Z (.neg A))))
  have h := Expr.identity E .zero v hv (by
    intro p
    simp only [E,C,B,A,Z,Expr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.zero,QComplex.mk.injEq]
    constructor <;> grind)
  exact h

private theorem small_sub_self (c : ComplexRaw) (hc : c.Valid)
    (r : Rat) (hr : 0 ≤ r) : Small (sub c c) r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m
    have h := (valid_ordered hc m).1
    change -r ≤ (c.compute m).hi.re + -(c.compute m).lo.re
    grind
  · intro n m
    have h := (valid_ordered hc n).1
    change (c.compute n).lo.re + -(c.compute n).hi.re ≤ r
    grind
  · intro n m
    have h := (valid_ordered hc m).2
    change -r ≤ (c.compute m).hi.im + -(c.compute m).lo.im
    grind
  · intro n m
    have h := (valid_ordered hc n).2
    change (c.compute n).lo.im + -(c.compute n).hi.im ≤ r
    grind

/-- A constructed holomorphicity witness, not a derivative field projection. -/
def affine_holomorphic (c b : ComplexRaw) (hc : c.Valid) (hb : b.Valid) :
    Holomorphic (affine c b hc hb) where
  openDomain := entireOpen _ (fun _ => True.intro)
  derivative := fun _ => c
  derivative_congr := fun _ _ _ _ _ => equiv_refl c hc
  continuousDerivative := {
    delta := fun _ _ _ _ => ⟨1, by decide⟩
    estimate := fun _ _ _ eps _ _ _ _ => small_sub_self c hc eps.val (Rat.le_of_lt eps.property) }
  atPoint := fun a ha hfa => {
    point_valid := ha
    point_mem := hfa
    derivative_valid := hc
    delta := fun _ => ⟨1, by decide⟩
    estimate := by
      intro eps H z hz _ _ _
      exact Small.congr (ofQComplex_valid _) (remainder_valid _ ha hc hz hfa True.intro)
        (equiv_symm (affine_remainder c b a z hc hb ha hz))
        (Small.zero (Rat.le_of_lt (Rat.mul_pos eps.property H.property))) }

/-- Squaring on arbitrary valid represented complex inputs. -/
def square : Map where
  domain := fun _ => True
  eval := fun z => mul z z
  valid := fun _ hz _ => mul_valid hz hz
  domain_congr := fun _ _ _ => Iff.rfl
  eval_congr := fun hz hw _ _ h => mul_equiv hz hw hz hw h h

theorem square_remainder (a z : ComplexRaw) (ha : a.Valid) (hz : z.Valid) :
    (remainder square a (add a a) z).Equiv (mul (sub z a) (sub z a)) := by
  let v : Nat → ComplexRaw := fun n => if n = 0 then a else z
  have hv : ∀ n, (v n).Valid := by intro n; dsimp [v]; split <;> assumption
  let A := Expr.var 0
  let Z := Expr.var 1
  let H := Expr.add Z (.neg A)
  let E := Expr.add (.add (.mul Z Z) (.neg (.mul A A))) (.neg (.mul (.add A A) H))
  have h := Expr.identity E (.mul H H) v hv (by
    intro p
    simp only [E,H,A,Z,Expr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
    constructor <;> grind)
  exact h

private theorem bounded_sample {z : ComplexRaw} {r : Rat}
    (hz : z.Valid) (h : Small z r) (hr : 0 ≤ r) (n : Nat) :
    ∃ p, Mem p (z.compute n) ∧ qabs p.re ≤ r ∧ qabs p.im ≤ r := by
  let p : QComplex := ⟨max (z.compute n).lo.re (-r), max (z.compute n).lo.im (-r)⟩
  have h1 := h.1 0 n
  have h2 := h.2.1 n 0
  have h3 := h.2.2.1 0 n
  have h4 := h.2.2.2 n 0
  have ho := valid_ordered hz n
  change -r ≤ (z.compute n).hi.re at h1
  change (z.compute n).lo.re ≤ r at h2
  change -r ≤ (z.compute n).hi.im at h3
  change (z.compute n).lo.im ≤ r at h4
  refine ⟨p, ?_, ?_, ?_⟩
  · dsimp [Mem,p]; simp only [QComplex.le_def]; change (z.compute n).lo.re ≤ (z.compute n).hi.re ∧ (z.compute n).lo.im ≤ (z.compute n).hi.im at ho
    grind
  · apply qabs_le_of_neg_le_le <;> dsimp [p] <;> grind
  · apply qabs_le_of_neg_le_le <;> dsimp [p] <;> grind

/-- Multiplication costs a factor of two in the coordinate maximum norm. -/
theorem Small.mul {z w : ComplexRaw} {r s : Rat}
    (hz : z.Valid) (hw : w.Valid) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : Small z r) (k : Small w s) : Small (mul z w) (2*r*s) := by
  have samples : ∀ n, ∃ p, Mem p ((ComplexRaw.mul z w).compute n) ∧
      qabs p.re ≤ 2*r*s ∧ qabs p.im ≤ 2*r*s := by
    intro n
    obtain ⟨p,hp,hpr,hpi⟩ := bounded_sample hz h hr n
    obtain ⟨q,hq,hqr,hqi⟩ := bounded_sample hw k hs n
    have hrr := rat_mul_le_mul_of_nonneg (qabs_nonneg p.re) hpr (qabs_nonneg q.re) hqr
    have hii := rat_mul_le_mul_of_nonneg (qabs_nonneg p.im) hpi (qabs_nonneg q.im) hqi
    have hri := rat_mul_le_mul_of_nonneg (qabs_nonneg p.re) hpr (qabs_nonneg q.im) hqi
    have hir := rat_mul_le_mul_of_nonneg (qabs_nonneg p.im) hpi (qabs_nonneg q.re) hqr
    refine ⟨QComplex.mul p q, QBox.mul_contains hp.1 hp.2 hq.1 hq.2, ?_, ?_⟩
    · have htri := qabs_sub_le (p.re*q.re) (p.im*q.im)
      rw [qabs_mul, qabs_mul] at htri
      change qabs (p.re*q.re-p.im*q.im) ≤ _
      grind
    · have htri := qabs_add_le (p.re*q.im) (p.im*q.re)
      rw [qabs_mul, qabs_mul] at htri
      change qabs (p.re*q.im+p.im*q.re) ≤ _
      grind
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m; obtain ⟨p,hp,hr,hi⟩ := samples m
    have := neg_qabs_le_self p.re
    exact Rat.le_trans (Rat.le_trans (Rat.neg_le_neg hr) this) hp.2.1
  · intro n m; obtain ⟨p,hp,hr,hi⟩ := samples n
    exact Rat.le_trans hp.1.1 (Rat.le_trans (self_le_qabs p.re) hr)
  · intro n m; obtain ⟨p,hp,hr,hi⟩ := samples m
    have := neg_qabs_le_self p.im
    exact Rat.le_trans (Rat.le_trans (Rat.neg_le_neg hi) this) hp.2.2
  · intro n m; obtain ⟨p,hp,hr,hi⟩ := samples n
    exact Rat.le_trans hp.1.2 (Rat.le_trans (self_le_qabs p.im) hi)

private theorem small_double_sub {a z : ComplexRaw} {r : Rat}
    (h : Small (sub z a) r) : Small (sub (add z z) (add a a)) (2*r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m
    have hm := h.1 n m
    change -r ≤ (z.compute m).hi.re + -(a.compute m).lo.re at hm
    change -(2*r) ≤ ((z.compute m).hi.re + (z.compute m).hi.re) + -((a.compute m).lo.re + (a.compute m).lo.re)
    grind
  · intro n m
    have hm := h.2.1 n m
    change (z.compute n).lo.re + -(a.compute n).hi.re ≤ r at hm
    change ((z.compute n).lo.re + (z.compute n).lo.re) + -((a.compute n).hi.re + (a.compute n).hi.re) ≤ 2*r
    grind
  · intro n m
    have hm := h.2.2.1 n m
    change -r ≤ (z.compute m).hi.im + -(a.compute m).lo.im at hm
    change -(2*r) ≤ ((z.compute m).hi.im + (z.compute m).hi.im) + -((a.compute m).lo.im + (a.compute m).lo.im)
    grind
  · intro n m
    have hm := h.2.2.2 n m
    change (z.compute n).lo.im + -(a.compute n).hi.im ≤ r at hm
    change ((z.compute n).lo.im + (z.compute n).lo.im) + -((a.compute n).hi.im + (a.compute n).hi.im) ≤ 2*r
    grind

/-- The square function is holomorphic with derivative twice the input and
an explicit error radius `eps/2` in the coordinate maximum norm. -/
def square_holomorphic : Holomorphic square where
  openDomain := entireOpen _ (fun _ => True.intro)
  derivative := fun a => add a a
  derivative_congr := fun _ _ _ _ h => add_equiv h h
  continuousDerivative := {
    delta := fun _ _ _ eps => ⟨eps.val / 2, by have := eps.property; grind⟩
    estimate := by
      intro a ha hfa eps z hz hfz h
      have hd := small_double_sub h
      exact hd.mono (by change 2*(eps.val/2) ≤ eps.val; grind) }
  atPoint := fun a ha hfa => {
    point_valid := ha
    point_mem := hfa
    derivative_valid := add_valid ha ha
    delta := fun eps => ⟨eps.val / 2, by have := eps.property; grind⟩
    estimate := by
      intro eps H z hz _ hH hza
      have hbound := Small.mul (sub_valid hz ha) (sub_valid hz ha)
        (Rat.le_of_lt H.property) (Rat.le_of_lt H.property) hza hza
      have hscale : 2*H.val*H.val ≤ eps.val*H.val := by
        have hlin : 2*H.val ≤ eps.val := by change H.val ≤ eps.val / 2 at hH; grind
        exact Rat.mul_le_mul_of_nonneg_right hlin (Rat.le_of_lt H.property)
      exact Small.congr (mul_valid (sub_valid hz ha) (sub_valid hz ha))
        (remainder_valid square ha (add_valid ha ha) hz hfa True.intro)
        (equiv_symm (square_remainder a z ha hz)) (hbound.mono hscale) }

end ComputableAnalysis.FunctionTheory
