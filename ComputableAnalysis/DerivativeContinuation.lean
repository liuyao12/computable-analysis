import ComputableAnalysis.DerivativeDefinition
import ComputableAnalysis.PointwiseContinuity
import ComputableAnalysis.HolomorphicPolynomial

/-! Continuous quotient extensions imply the existing quantitative derivative
estimates and construct new extensions under algebra and composition. -/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw Continuation

private def halfTolerance (eps : QPos) : QPos :=
  ⟨eps.val/2, by have := eps.property; grind⟩

private theorem quotient_remainder {f : Map} {a d : ComplexRaw}
    (h : DerivativeAt f a d) (z : ComplexRaw) (hz : z.Valid) (hfz : f.domain z) :
    (remainder f a d z).Equiv (ComplexRaw.mul (sub z a) (sub (h.quotient z) d)) := by
  have hzq := h.quotient_valid z hz hfz
  have hΔ := sub_valid hz h.point_valid
  have first := sub_congr (h.factorization z hz hfz)
    (equiv_refl _ (mul_valid h.derivative_valid hΔ))
  let v : Nat → ComplexRaw := fun i => if i=0 then sub z a else if i=1 then h.quotient z else d
  have hv : ∀ i, (v i).Valid := by
    intro i; dsimp [v]; split
    · exact hΔ
    · split
      · exact hzq
      · exact h.derivative_valid
  have second := PolynomialExpr.identity
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 0))))
    (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) v hv (by
      intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)
  exact equiv_trans (remainder_valid f h.point_valid h.derivative_valid hz h.point_mem hfz)
    (sub_valid (mul_valid hΔ hzq) (mul_valid h.derivative_valid hΔ))
    (mul_valid hΔ (sub_valid hzq h.derivative_valid)) first second

/-- The continuous quotient proves the quantitative remainder law. -/
def DerivativeAt.toEstimate {f : Map} {a d : ComplexRaw} (h : DerivativeAt f a d) :
    HasDerivativeAt f a d where
  point_valid := h.point_valid
  point_mem := h.point_mem
  derivative_valid := h.derivative_valid
  delta := fun eps => h.quotient_continuous.delta (halfTolerance eps)
  estimate := by
    intro eps H z hz hfz hH hza
    have hc := h.quotient_continuous.estimate (halfTolerance eps) z hz hfz (hza.mono hH)
    have hq := h.quotient_valid z hz hfz
    have hqa := h.quotient_valid a h.point_valid h.point_mem
    have hqd := Small.congr (sub_valid hq hqa) (sub_valid hq h.derivative_valid)
      (sub_congr (equiv_refl _ hq) h.value_at) hc
    have hb := hza.mul (sub_valid hz h.point_valid) (sub_valid hq h.derivative_valid)
      (Rat.le_of_lt H.property) (Rat.le_of_lt (halfTolerance eps).property) hqd
    exact Small.congr (mul_valid (sub_valid hz h.point_valid) (sub_valid hq h.derivative_valid))
      (remainder_valid f h.point_valid h.derivative_valid hz h.point_mem hfz)
      (equiv_symm (quotient_remainder h z hz hfz))
      (hb.mono (by dsimp [halfTolerance]; grind))

/-- Differentiability implies continuity of the original function at the center. -/
def DerivativeAt.continuous {f : Map} {a d : ComplexRaw} (h : DerivativeAt f a d) :
    ContinuousAt f.domain f.eval a := h.toEstimate.continuous

theorem DerivativeAt.unique {f : Map} (o : OpenDomain f) {a d e : ComplexRaw}
    (h : DerivativeAt f a d) (k : DerivativeAt f a e) : d.Equiv e :=
  h.toEstimate.unique o k.toEstimate

/-- Only the derivative name changes; the same quotient computation is retained. -/
def DerivativeAt.congrDerivative {f : Map} {a d e : ComplexRaw}
    (h : DerivativeAt f a d) (he : e.Valid) (hde : d.Equiv e) : DerivativeAt f a e where
  quotient := h.quotient
  quotient_valid := h.quotient_valid
  quotient_congr := h.quotient_congr
  quotient_continuous := h.quotient_continuous
  derivative_valid := he
  value_at := equiv_trans (h.quotient_valid a h.point_valid h.point_mem) h.derivative_valid he h.value_at hde
  factorization := h.factorization

/-- The same quotient computation works at an equivalent center. -/
def DerivativeAt.congrPoint {f : Map} {a b d : ComplexRaw}
    (h : DerivativeAt f a d) (hb : b.Valid) (hab : a.Equiv b) : DerivativeAt f b d where
  quotient := h.quotient
  quotient_valid := h.quotient_valid
  quotient_congr := h.quotient_congr
  quotient_continuous := h.quotient_continuous.congrPoint hb hab f.domain_congr
    h.quotient_valid h.quotient_congr
  derivative_valid := h.derivative_valid
  value_at := by
    have hfb := (f.domain_congr h.point_valid hb hab).mp h.point_mem
    exact equiv_trans (h.quotient_valid b hb hfb) (h.quotient_valid a h.point_valid h.point_mem)
      h.derivative_valid (equiv_symm (h.quotient_congr h.point_valid hb h.point_mem hfb hab)) h.value_at
  factorization := by
    intro z hz hfz
    have hfb := (f.domain_congr h.point_valid hb hab).mp h.point_mem
    have hfa := f.valid a h.point_valid h.point_mem
    have hfv := f.valid b hb hfb
    have hvz := f.valid z hz hfz
    have hq := h.quotient_valid z hz hfz
    have first := sub_congr (equiv_refl _ hvz)
      (equiv_symm (f.eval_congr h.point_valid hb h.point_mem hfb hab))
    have last := mul_equiv (sub_valid hz h.point_valid) (sub_valid hz hb) hq hq
      (sub_congr (equiv_refl z hz) hab) (equiv_refl _ hq)
    exact equiv_trans (sub_valid hvz hfv) (sub_valid hvz hfa) (mul_valid (sub_valid hz hb) hq)
      first (equiv_trans (sub_valid hvz hfa) (mul_valid (sub_valid hz h.point_valid) hq)
        (mul_valid (sub_valid hz hb) hq) (h.factorization z hz hfz) last)

/-- Transfer an actual quotient extension to an equivalent evaluator and domain. -/
def DerivativeAt.congrMap {f g : Map} {a d : ComplexRaw}
    (h : DerivativeAt f a d)
    (domains : ∀ z, f.domain z ↔ g.domain z)
    (agree : ∀ z, z.Valid → f.domain z → (f.eval z).Equiv (g.eval z)) : DerivativeAt g a d where
  quotient := h.quotient
  quotient_valid := fun z hz hgz => h.quotient_valid z hz ((domains z).mpr hgz)
  quotient_congr := fun hz hw hgz hgw he => h.quotient_congr hz hw
    ((domains _).mpr hgz) ((domains _).mpr hgw) he
  quotient_continuous := h.quotient_continuous.restrict (fun z hgz => (domains z).mpr hgz)
    ((domains a).mp h.point_mem)
  derivative_valid := h.derivative_valid
  value_at := h.value_at
  factorization := by
    intro z hz hgz
    have hfz := (domains z).mpr hgz
    have hga := (domains a).mp h.point_mem
    exact equiv_trans (sub_valid (g.valid z hz hgz) (g.valid a h.point_valid hga))
      (sub_valid (f.valid z hz hfz) (f.valid a h.point_valid h.point_mem))
      (mul_valid (sub_valid hz h.point_valid) (h.quotient_valid z hz hfz))
      (equiv_symm (sub_congr (agree z hz hfz) (agree a h.point_valid h.point_mem)))
      (h.factorization z hz hfz)

/-- Constant functions have the literal zero quotient extension. -/
def derivativeAt_constant (c a : ComplexRaw) (hc : c.Valid) (ha : a.Valid) :
    DerivativeAt (Map.constant c hc) a zero where
  quotient := fun _ => zero
  quotient_valid := fun _ _ _ => ofQComplex_valid _
  quotient_congr := fun _ _ _ _ _ => equiv_refl zero (ofQComplex_valid _)
  quotient_continuous := {
    point_valid := ha
    point_mem := True.intro
    delta := fun eps => eps
    estimate := fun eps _ _ _ _ => Small.sub_self zero (ofQComplex_valid _) (Rat.le_of_lt eps.property) }
  derivative_valid := ofQComplex_valid _
  value_at := equiv_refl zero (ofQComplex_valid _)
  factorization := by
    intro z hz _
    exact PolynomialExpr.identity (.add (.var 0) (.neg (.var 0)))
      (.mul (.add (.var 1) (.neg (.var 2))) (.lit QComplex.zero))
      (fun i => if i=0 then c else if i=1 then z else a)
      (by intro i; split <;> first | assumption | (split <;> assumption)) (by
        intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.zero,QComplex.mk.injEq]
        constructor <;> grind)

/-- The identity function has the literal constant-one quotient extension. -/
def derivativeAt_identity (a : ComplexRaw) (ha : a.Valid) :
    DerivativeAt Map.identity a one where
  quotient := fun _ => one
  quotient_valid := fun _ _ _ => ofQComplex_valid _
  quotient_congr := fun _ _ _ _ _ => equiv_refl one (ofQComplex_valid _)
  quotient_continuous := {
    point_valid := ha
    point_mem := True.intro
    delta := fun eps => eps
    estimate := fun eps _ _ _ _ => Small.sub_self one (ofQComplex_valid _) (Rat.le_of_lt eps.property) }
  derivative_valid := ofQComplex_valid _
  value_at := equiv_refl one (ofQComplex_valid _)
  factorization := by
    intro z hz _
    exact PolynomialExpr.identity (.add (.var 0) (.neg (.var 1)))
      (.mul (.add (.var 0) (.neg (.var 1))) (.lit QComplex.one))
      (fun i => if i=0 then z else a) (by intro i; split <;> assumption) (by
        intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.one,QComplex.mk.injEq]
        constructor <;> grind)

private def values (xs : List Point) (i : Nat) : ComplexRaw :=
  (xs[i]?.getD ⟨zero,ofQComplex_valid _⟩).val
private theorem values_valid (xs : List Point) (i : Nat) : (values xs i).Valid :=
  (xs[i]?.getD ⟨zero,ofQComplex_valid _⟩).property

private theorem sum_difference (u v x y : ComplexRaw)
    (hu : u.Valid) (hv : v.Valid) (hx : x.Valid) (hy : y.Valid) :
    (sub (ComplexRaw.add u v) (ComplexRaw.add x y)).Equiv (ComplexRaw.add (sub u x) (sub v y)) :=
  PolynomialExpr.identity
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
    (values [⟨u,hu⟩,⟨v,hv⟩,⟨x,hx⟩,⟨y,hy⟩]) (values_valid _) (by
      intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mk.injEq]
      constructor <;> grind)

private theorem factor_sum (h u v : ComplexRaw) (hh : h.Valid) (hu : u.Valid) (hv : v.Valid) :
    (ComplexRaw.add (ComplexRaw.mul h u) (ComplexRaw.mul h v)).Equiv (ComplexRaw.mul h (ComplexRaw.add u v)) :=
  PolynomialExpr.identity
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
    (.mul (.var 0) (.add (.var 1) (.var 2)))
    (values [⟨h,hh⟩,⟨u,hu⟩,⟨v,hv⟩]) (values_valid _) (by
      intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

/-- The sum rule constructs the sum of the two quotient extensions. -/
def DerivativeAt.add {f g : Map} {a d e : ComplexRaw}
    (hf : DerivativeAt f a d) (hg : DerivativeAt g a e) :
    DerivativeAt (f.add g) a (ComplexRaw.add d e) where
  quotient := fun z => ComplexRaw.add (hf.quotient z) (hg.quotient z)
  quotient_valid := fun z hz h => add_valid (hf.quotient_valid z hz h.1) (hg.quotient_valid z hz h.2)
  quotient_congr := fun hz hw h1 h2 he => add_equiv
    (hf.quotient_congr hz hw h1.1 h2.1 he) (hg.quotient_congr hz hw h1.2 h2.2 he)
  quotient_continuous :=
    (hf.quotient_continuous.restrict (fun _ h => h.1) ⟨hf.point_mem,hg.point_mem⟩).add
      (fun z hz h => hf.quotient_valid z hz h.1) (fun z hz h => hg.quotient_valid z hz h.2)
      (hg.quotient_continuous.restrict (fun _ h => h.2) ⟨hf.point_mem,hg.point_mem⟩)
  derivative_valid := add_valid hf.derivative_valid hg.derivative_valid
  value_at := add_equiv hf.value_at hg.value_at
  factorization := by
    intro z hz h
    have vf := f.valid z hz h.1
    have vg := g.valid z hz h.2
    have va := f.valid a hf.point_valid hf.point_mem
    have vb := g.valid a hg.point_valid hg.point_mem
    have vq := hf.quotient_valid z hz h.1
    have vr := hg.quotient_valid z hz h.2
    have vΔ := sub_valid hz hf.point_valid
    have first := sum_difference _ _ _ _ vf vg va vb
    have second := add_equiv (hf.factorization z hz h.1) (hg.factorization z hz h.2)
    have last := factor_sum _ _ _ vΔ vq vr
    exact equiv_trans (sub_valid (add_valid vf vg) (add_valid va vb))
      (add_valid (sub_valid vf va) (sub_valid vg vb))
      (mul_valid vΔ (add_valid vq vr)) first
      (equiv_trans (add_valid (sub_valid vf va) (sub_valid vg vb))
        (add_valid (mul_valid vΔ vq) (mul_valid vΔ vr))
        (mul_valid vΔ (add_valid vq vr)) second last)

private theorem product_difference (u v x y : ComplexRaw)
    (hu : u.Valid) (hv : v.Valid) (hx : x.Valid) (hy : y.Valid) :
    (sub (ComplexRaw.mul u v) (ComplexRaw.mul x y)).Equiv (ComplexRaw.add (ComplexRaw.mul (sub u x) v) (ComplexRaw.mul x (sub v y))) :=
  PolynomialExpr.identity
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
    (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 1))
      (.mul (.var 2) (.add (.var 1) (.neg (.var 3)))))
    (values [⟨u,hu⟩,⟨v,hv⟩,⟨x,hx⟩,⟨y,hy⟩]) (values_valid _) (by
      intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

private theorem product_factor (h u v x y : ComplexRaw)
    (hh : h.Valid) (hu : u.Valid) (hv : v.Valid) (hx : x.Valid) (hy : y.Valid) :
    (ComplexRaw.add (ComplexRaw.mul (ComplexRaw.mul h u) v) (ComplexRaw.mul x (ComplexRaw.mul h y))).Equiv (ComplexRaw.mul h (ComplexRaw.add (ComplexRaw.mul u v) (ComplexRaw.mul x y))) :=
  PolynomialExpr.identity
    (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.mul (.var 0) (.var 4))))
    (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
    (values [⟨h,hh⟩,⟨u,hu⟩,⟨v,hv⟩,⟨x,hx⟩,⟨y,hy⟩]) (values_valid _) (by
      intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

/-- The product quotient is `Q_f(z) g(z) + f(a) Q_g(z)`. -/
def DerivativeAt.mul {f g : Map} {a d e : ComplexRaw}
    (hf : DerivativeAt f a d) (hg : DerivativeAt g a e) :
    DerivativeAt (f.mul g) a (ComplexRaw.add (ComplexRaw.mul d (g.eval a)) (ComplexRaw.mul (f.eval a) e)) := by
  let D := (f.mul g).domain
  have ha := hf.point_valid
  have hDa : D a := ⟨hf.point_mem,hg.point_mem⟩
  have vf := f.valid a ha hf.point_mem
  have vg := g.valid a ha hg.point_mem
  let cqf := hf.quotient_continuous.restrict (fun _ h => h.1) hDa
  let cqg := hg.quotient_continuous.restrict (fun _ h => h.2) hDa
  let cg := hg.continuous.restrict (fun _ h => h.2) hDa
  let cf : ContinuousAt D (fun _ => f.eval a) a := {
    point_valid := ha, point_mem := hDa, delta := id,
    estimate := fun eps _ _ _ _ => Small.sub_self _ vf (Rat.le_of_lt eps.property) }
  have left := cqf.mul (fun z hz h => hf.quotient_valid z hz h.1) (fun z hz h => g.valid z hz h.2) cg
  have right := cf.mul (fun _ _ _ => vf) (fun z hz h => hg.quotient_valid z hz h.2) cqg
  refine {
    quotient := fun z => ComplexRaw.add (ComplexRaw.mul (hf.quotient z) (g.eval z)) (ComplexRaw.mul (f.eval a) (hg.quotient z))
    quotient_valid := fun z hz h => add_valid
      (mul_valid (hf.quotient_valid z hz h.1) (g.valid z hz h.2))
      (mul_valid vf (hg.quotient_valid z hz h.2))
    quotient_congr := fun hz hw h1 h2 he => add_equiv
      (mul_equiv (hf.quotient_valid _ hz h1.1) (hf.quotient_valid _ hw h2.1)
        (g.valid _ hz h1.2) (g.valid _ hw h2.2)
        (hf.quotient_congr hz hw h1.1 h2.1 he) (g.eval_congr hz hw h1.2 h2.2 he))
      (mul_equiv vf vf (hg.quotient_valid _ hz h1.2) (hg.quotient_valid _ hw h2.2)
        (equiv_refl _ vf) (hg.quotient_congr hz hw h1.2 h2.2 he))
    quotient_continuous := left.add
      (fun z hz h => mul_valid (hf.quotient_valid z hz h.1) (g.valid z hz h.2))
      (fun z hz h => mul_valid vf (hg.quotient_valid z hz h.2)) right
    derivative_valid := add_valid (mul_valid hf.derivative_valid vg) (mul_valid vf hg.derivative_valid)
    value_at := add_equiv
      (mul_equiv (hf.quotient_valid a ha hf.point_mem) hf.derivative_valid vg vg hf.value_at (equiv_refl _ vg))
      (mul_equiv vf vf (hg.quotient_valid a ha hg.point_mem) hg.derivative_valid (equiv_refl _ vf) hg.value_at)
    factorization := ?_ }
  intro z hz h
  have vzf := f.valid z hz h.1
  have vzg := g.valid z hz h.2
  have vq := hf.quotient_valid z hz h.1
  have vr := hg.quotient_valid z hz h.2
  have vΔ := sub_valid hz ha
  have first := product_difference _ _ _ _ vzf vzg vf vg
  have second := add_equiv
    (mul_equiv (sub_valid vzf vf) (mul_valid vΔ vq) vzg vzg (hf.factorization z hz h.1) (equiv_refl _ vzg))
    (mul_equiv vf vf (sub_valid vzg vg) (mul_valid vΔ vr) (equiv_refl _ vf) (hg.factorization z hz h.2))
  have last := product_factor _ _ _ _ _ vΔ vq vzg vf vr
  exact equiv_trans (sub_valid (mul_valid vzf vzg) (mul_valid vf vg))
    (add_valid (mul_valid (sub_valid vzf vf) vzg) (mul_valid vf (sub_valid vzg vg)))
    (mul_valid vΔ (add_valid (mul_valid vq vzg) (mul_valid vf vr))) first
    (equiv_trans (add_valid (mul_valid (sub_valid vzf vf) vzg) (mul_valid vf (sub_valid vzg vg)))
      (add_valid (mul_valid (mul_valid vΔ vq) vzg) (mul_valid vf (mul_valid vΔ vr)))
      (mul_valid vΔ (add_valid (mul_valid vq vzg) (mul_valid vf vr))) second last)

private theorem chain_factor (h u v : ComplexRaw) (hh : h.Valid) (hu : u.Valid) (hv : v.Valid) :
    (ComplexRaw.mul (ComplexRaw.mul h u) v).Equiv (ComplexRaw.mul h (ComplexRaw.mul v u)) :=
  PolynomialExpr.identity (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 0) (.mul (.var 2) (.var 1)))
    (values [⟨h,hh⟩,⟨u,hu⟩,⟨v,hv⟩]) (values_valid _) (by
      intro p; simp only [PolynomialExpr.rational,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

/-- The chain quotient is `Q_g(f(z)) Q_f(z)`, on the genuine inverse-image domain. -/
def DerivativeAt.comp {f g : Map} {a d e : ComplexRaw}
    (hf : DerivativeAt f a d) (hg : DerivativeAt g (f.eval a) e) :
    DerivativeAt (g.comp f) a (ComplexRaw.mul e d) := by
  let D := (g.comp f).domain
  have ha := hf.point_valid
  have hDa : D a := ⟨hf.point_mem,hg.point_mem⟩
  have vf := f.valid a ha hf.point_mem
  have qf := hf.quotient_continuous.restrict (fun _ h => h.1) hDa
  have cf := hf.continuous.restrict (fun _ h => h.1) hDa
  have qg := cf.comp (fun z hz h => f.valid z hz h.1) (fun _ _ h => h.2) hg.quotient_continuous
  refine {
    quotient := fun z => ComplexRaw.mul (hg.quotient (f.eval z)) (hf.quotient z)
    quotient_valid := fun z hz h => mul_valid
      (hg.quotient_valid _ (f.valid z hz h.1) h.2) (hf.quotient_valid z hz h.1)
    quotient_congr := fun hz hw h1 h2 he => mul_equiv
      (hg.quotient_valid _ (f.valid _ hz h1.1) h1.2) (hg.quotient_valid _ (f.valid _ hw h2.1) h2.2)
      (hf.quotient_valid _ hz h1.1) (hf.quotient_valid _ hw h2.1)
      (hg.quotient_congr (f.valid _ hz h1.1) (f.valid _ hw h2.1) h1.2 h2.2
        (f.eval_congr hz hw h1.1 h2.1 he)) (hf.quotient_congr hz hw h1.1 h2.1 he)
    quotient_continuous := qg.mul
      (fun z hz h => hg.quotient_valid _ (f.valid z hz h.1) h.2)
      (fun z hz h => hf.quotient_valid z hz h.1) qf
    derivative_valid := mul_valid hg.derivative_valid hf.derivative_valid
    value_at := mul_equiv (hg.quotient_valid _ vf hg.point_mem) hg.derivative_valid
      (hf.quotient_valid a ha hf.point_mem) hf.derivative_valid hg.value_at hf.value_at
    factorization := ?_ }
  intro z hz h
  have vzf := f.valid z hz h.1
  have vq := hf.quotient_valid z hz h.1
  have vr := hg.quotient_valid _ vzf h.2
  have vΔ := sub_valid hz ha
  have first := hg.factorization _ vzf h.2
  have second := mul_equiv (sub_valid vzf vf) (mul_valid vΔ vq) vr vr
    (hf.factorization z hz h.1) (equiv_refl _ vr)
  have last := chain_factor _ _ _ vΔ vq vr
  exact equiv_trans (sub_valid (g.valid _ vzf h.2) (g.valid _ vf hg.point_mem))
    (mul_valid (sub_valid vzf vf) vr) (mul_valid vΔ (mul_valid vr vq)) first
    (equiv_trans (mul_valid (sub_valid vzf vf) vr) (mul_valid (mul_valid vΔ vq) vr)
      (mul_valid vΔ (mul_valid vr vq)) second last)

def DifferentiableOn.continuous {f : Map} (h : DifferentiableOn f) : ContinuousOn f.domain f.eval :=
  .ofAtPoint fun a ha hfa => (h.atPoint a ha hfa).continuous

/-- Upgrade the pointwise foundation only when the extra holomorphic data are supplied. -/
def DifferentiableOn.holomorphic {f : Map} (h : DifferentiableOn f)
    (o : OpenDomain f) (c : ContinuousOn f.domain h.derivative) : Holomorphic f where
  openDomain := o
  derivative := h.derivative
  atPoint := fun a ha hfa => (h.atPoint a ha hfa).toEstimate
  derivative_congr := h.derivative_congr
  continuousDerivative := c

end ComputableAnalysis.FunctionTheory
