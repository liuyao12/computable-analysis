import ComputableAnalysis.ModularForms.CMNomeQuadraticDecay163

/-! Representation and radius invariance of the constructed normalized Fourier expressions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem local_guard (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) : 4*r≤(1:Rat)/2 := by grind only
private theorem ratio_guard (r : Rat) (hr : 0≤r) (hg : 128*r≤(1:Rat)/2) (k : Nat) (hk : k=3 ∨ k=5) :
    weightedLambertRatio r k≤(1:Rat)/2 := by
  unfold weightedLambertRatio
  rcases hk with h | h
  · rw [h,show (2:Rat)^3=8 by decide +kernel]; grind only
  · rw [h,show (2:Rat)^5=32 by decide +kernel]; grind only

/-- Actual normalized weight-four values agree across valid representations and radius choices. -/
theorem nomeEisensteinFour_congr (q w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrg : 128*r≤(1:Rat)/2) (hsg : 128*s≤(1:Rat)/2)
    (hq : Small q.val r) (hw : Small w.val s) (he : q.val.Equiv w.val) :
    (nomeEisensteinFour q r hr hrg hq).val.Equiv (nomeEisensteinFour w s hs hsg hw).val :=
  add_equiv (equiv_refl one (ofQComplex_valid _))
    (scaleRat_equiv (r := (240:Rat)) (weightedLambertSum_congr q w r s 3 hr hs
      (local_guard r hr hrg) (local_guard s hs hsg) hq hw
      (ratio_guard r hr hrg 3 (Or.inl rfl)) (ratio_guard s hs hsg 3 (Or.inl rfl)) he))

/-- Actual normalized weight-six values agree across valid representations and radius choices. -/
theorem nomeEisensteinSix_congr (q w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrg : 128*r≤(1:Rat)/2) (hsg : 128*s≤(1:Rat)/2)
    (hq : Small q.val r) (hw : Small w.val s) (he : q.val.Equiv w.val) :
    (nomeEisensteinSix q r hr hrg hq).val.Equiv (nomeEisensteinSix w s hs hsg hw).val :=
  add_equiv (equiv_refl one (ofQComplex_valid _))
    (scaleRat_equiv (r := (-504:Rat)) (weightedLambertSum_congr q w r s 5 hr hs
      (local_guard r hr hrg) (local_guard s hs hsg) hq hw
      (ratio_guard r hr hrg 5 (Or.inr rfl)) (ratio_guard s hs hsg 5 (Or.inr rfl)) he))

/-- The actual Fourier discriminant numerator is representation and radius invariant. -/
theorem nomeDiscriminantNumerator_congr (q w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrg : 128*r≤(1:Rat)/2) (hsg : 128*s≤(1:Rat)/2)
    (hq : Small q.val r) (hw : Small w.val s) (he : q.val.Equiv w.val) :
    (nomeDiscriminantNumerator q r hr hrg hq).val.Equiv (nomeDiscriminantNumerator w s hs hsg hw).val :=
  FunctionTheory.sub_congr
    (LocalODE.power_congr _ _ (nomeEisensteinFour q r hr hrg hq).property (nomeEisensteinFour w s hs hsg hw).property
      (nomeEisensteinFour_congr q w r s hr hs hrg hsg hq hw he) 3)
    (LocalODE.power_congr _ _ (nomeEisensteinSix q r hr hrg hq).property (nomeEisensteinSix w s hs hsg hw).property
      (nomeEisensteinSix_congr q w r s hr hs hrg hsg hq hw he) 2)

/-- The actual normalized Fourier discriminant is representation and radius invariant. -/
theorem nomeModularDiscriminant_congr (q w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrg : 128*r≤(1:Rat)/2) (hsg : 128*s≤(1:Rat)/2)
    (hq : Small q.val r) (hw : Small w.val s) (he : q.val.Equiv w.val) :
    (nomeModularDiscriminant q r hr hrg hq).val.Equiv (nomeModularDiscriminant w s hs hsg hw).val :=
  scaleRat_equiv (r := (1/1728:Rat)) (nomeDiscriminantNumerator_congr q w r s hr hs hrg hsg hq hw he)

/-- The already constructed CM discriminant has the sharper actual leading-term bound. -/
theorem cmFourierDiscriminant163_nome_bound_fortySeven :
    Small (sub cmFourierDiscriminant163.val (nome.eval cmScalar163 cmPoint163_upper).val)
      (9000*(1/140737488355328)*(1/140737488355328)) := by
  let q := nome.eval cmScalar163 cmPoint163_upper
  let d := nomeModularDiscriminant q (1/140737488355328) (by decide +kernel) (by decide +kernel)
    nome_cm163_small_fortySeven_power
  have hd := nomeModularDiscriminant_linear_bound q (1/140737488355328) (by decide +kernel)
    (by decide +kernel) nome_cm163_small_fortySeven_power (by decide +kernel)
  have he := nomeModularDiscriminant_congr q q (1/140737488355328) (1/68719476736)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    nome_cm163_small_fortySeven_power nome_cm163_small_thirtySix_power (equiv_refl q.val q.property)
  exact Small.congr (sub_valid d.property q.property) (sub_valid cmFourierDiscriminant163.property q.property)
    (FunctionTheory.sub_congr he (equiv_refl q.val q.property)) hd

end ComputableAnalysis.ModularForms
