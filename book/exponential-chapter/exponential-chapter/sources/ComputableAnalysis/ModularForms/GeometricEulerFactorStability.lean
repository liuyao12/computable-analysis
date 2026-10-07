import ComputableAnalysis.ModularForms.GeometricEulerExponentialFactor

/-! Sharp coordinate stability for a rational geometric Euler factor. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private def Mem (p : QComplex) (B : QBox) : Prop := B.lo ≤ p ∧ p ≤ B.hi

private theorem boundedCoordinateSample (z : ComplexRaw) (hz : z.Valid) (E : Rat)
    (hE : 0 ≤ E) (h : Small z E) (n : Nat) :
    ∃ p, Mem p (z.compute n) ∧ qabs p.re ≤ E ∧ qabs p.im ≤ E := by
  let p : QComplex := ⟨max (z.compute n).lo.re (-E), max (z.compute n).lo.im (-E)⟩
  have h1 := h.1 0 n
  have h2 := h.2.1 n 0
  have h3 := h.2.2.1 0 n
  have h4 := h.2.2.2 n 0
  have ho := valid_ordered hz n
  change -E ≤ (z.compute n).hi.re at h1
  change (z.compute n).lo.re ≤ E at h2
  change -E ≤ (z.compute n).hi.im at h3
  change (z.compute n).lo.im ≤ E at h4
  refine ⟨p, ?_, ?_, ?_⟩
  · dsimp [Mem,p]
    simp only [QComplex.le_def]
    change (z.compute n).lo.re ≤ (z.compute n).hi.re ∧
      (z.compute n).lo.im ≤ (z.compute n).hi.im at ho
    grind
  · apply qabs_le_of_neg_le_le <;> dsimp [p] <;> grind
  · apply qabs_le_of_neg_le_le <;> dsimp [p] <;> grind

theorem geometricEulerFactor_mul_small (t h E : Rat) (z : ComplexRaw)
    (hz : z.Valid) (hh : 0 ≤ h) (hE : 0 ≤ E) (hs : Small z E) :
    Small (mul (geometricEulerFactor t h).val z) ((1+2*h)*E) := by
  have samples : ∀ n, ∃ p, Mem p ((mul (geometricEulerFactor t h).val z).compute n) ∧
      qabs p.re ≤ (1+2*h)*E ∧ qabs p.im ≤ (1+2*h)*E := by
    intro n
    obtain ⟨p,hp,hpr,hpi⟩ := boundedCoordinateSample z hz E hE hs n
    let q : QComplex := ⟨1,h*(2/(1+t*t))⟩
    have hm := Rat.mul_le_mul_of_nonneg_left (geometricRotationSpeed_bound t) hh
    have hc : qabs (h*(2/(1+t*t))) ≤ 2*h := by
      rw [qabs_mul,qabs_eq_self_of_nonneg hh]
      grind only
    have hr := rat_mul_le_mul_of_nonneg (qabs_nonneg (h*(2/(1+t*t)))) hc
      (qabs_nonneg p.re) hpr
    have hi := rat_mul_le_mul_of_nonneg (qabs_nonneg (h*(2/(1+t*t)))) hc
      (qabs_nonneg p.im) hpi
    have hq : Mem q ((geometricEulerFactor t h).val.compute n) :=
      ⟨⟨Rat.le_refl,Rat.le_refl⟩,⟨Rat.le_refl,Rat.le_refl⟩⟩
    refine ⟨QComplex.mul q p, QBox.mul_contains hq.1 hq.2 hp.1 hp.2, ?_, ?_⟩
    · have ht := qabs_sub_le p.re (h*(2/(1+t*t))*p.im)
      rw [qabs_mul] at ht
      change qabs (1*p.re-h*(2/(1+t*t))*p.im) ≤ _
      grind only
    · have ht := qabs_add_le p.im (h*(2/(1+t*t))*p.re)
      rw [qabs_mul] at ht
      change qabs (1*p.im+h*(2/(1+t*t))*p.re) ≤ _
      grind only
  refine ⟨?_,?_,?_,?_⟩
  · intro n m; obtain ⟨p,hp,hr,hi⟩ := samples m
    exact Rat.le_trans (Rat.le_trans (Rat.neg_le_neg hr) (neg_qabs_le_self p.re)) hp.2.1
  · intro n m; obtain ⟨p,hp,hr,hi⟩ := samples n
    exact Rat.le_trans hp.1.1 (Rat.le_trans (self_le_qabs p.re) hr)
  · intro n m; obtain ⟨p,hp,hr,hi⟩ := samples m
    exact Rat.le_trans (Rat.le_trans (Rat.neg_le_neg hi) (neg_qabs_le_self p.im)) hp.2.2
  · intro n m; obtain ⟨p,hp,hr,hi⟩ := samples n
    exact Rat.le_trans hp.1.2 (Rat.le_trans (self_le_qabs p.im) hi)

theorem geometricExponentialProduct_error_step (t h E M : Rat) (p q : ComplexRaw)
    (hp : p.Valid) (hq : q.Valid) (hh : 0 ≤ h) (h1 : h ≤ 1)
    (hE : 0 ≤ E) (hM : 0 ≤ M) (he : Small (sub p q) E) (hm : Small p M) :
    Small (sub (mul (entireExponentialValue (geometricAngularIncrement t h)).val p)
      (mul (geometricEulerFactor t h).val q))
      ((1+2*h)*E + 2*(4*exponentialQuadraticConstant geometricFactorRadius*h*h)*M) := by
  let a := (entireExponentialValue (geometricAngularIncrement t h)).val
  let f := (geometricEulerFactor t h).val
  have ha : a.Valid := (entireExponentialValue _).property
  have hf : f.Valid := (geometricEulerFactor t h).property
  have hid : (sub (mul a p) (mul f q)).Equiv
      (add (mul f (sub p q)) (mul (sub a f) p)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (mul_valid ha hp) (mul_valid hf hq))
      (hright := add_valid (mul_valid hf (sub_valid hp hq)) (mul_valid (sub_valid ha hf) hp))
    change ComplexRawQuotient.ofRaw a ha * ComplexRawQuotient.ofRaw p hp +
      -(ComplexRawQuotient.ofRaw f hf * ComplexRawQuotient.ofRaw q hq) =
      ComplexRawQuotient.ofRaw f hf *
        (ComplexRawQuotient.ofRaw p hp + -ComplexRawQuotient.ofRaw q hq) +
      (ComplexRawQuotient.ofRaw a ha + -ComplexRawQuotient.ofRaw f hf) *
        ComplexRawQuotient.ofRaw p hp
    grind only
  have hc := exponentialQuadraticConstant_nonnegative geometricFactorRadius
  have hd : 0 ≤ 4*exponentialQuadraticConstant geometricFactorRadius*h*h :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hc) hh) hh
  have hl := geometricEulerFactor_mul_small t h E (sub p q) (sub_valid hp hq) hh hE he
  have hr := Small.mul (sub_valid ha hf) hp hd hM
    (geometricEulerFactor_exponential_error t h hh h1) hm
  exact Small.congr (add_valid (mul_valid hf (sub_valid hp hq)) (mul_valid (sub_valid ha hf) hp))
    (sub_valid (mul_valid ha hp) (mul_valid hf hq)) (equiv_symm hid) (LocalODE.small_add hl hr)

end ComputableAnalysis.ModularForms
