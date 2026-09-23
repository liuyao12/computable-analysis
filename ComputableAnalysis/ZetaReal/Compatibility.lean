import ComputableAnalysis.ZetaReal.Series

namespace ComputableAnalysis.ZetaReal

theorem atReal_equiv_raw {q m : Nat} (hq : 0 < q) (s : Real)
    (hs : ∀ n, subintervalOf (s.compute n) (lower q) ((m : Rat)+2))
    (t : Rat) (ht : InChart q m t) (heq : s.preferred.Equiv (RealRaw.ofRat t)) :
    (atReal q m hq s hs).preferred.Equiv (raw q m hq t) := by
  apply (continuous q m hq).applyRealRaw_equiv_of_applyCandidate_overlap
  · exact raw_valid hq ht
  · intro n
    let i := (continuous q m hq).inputStage s.preferred s.valid n
    have hp := (RealRaw.compareAt_overlap_iff _ _ i n).1
      (RealRaw.allStagesOverlap_of_equiv s.valid (RealRaw.ofRat_valid t) heq i n)
    have hc := imageBox_contains hq (s.compute i) (hs i) ht n hp.1 hp.2
    have ho := (raw_valid hq ht).2.1 n n (Nat.le_refl n)
    exact ⟨Rat.le_trans hc.1 ho.2.1, Rat.le_trans ho.2.1 hc.2⟩

/-- On rational inputs the public real function agrees with every admissible chart. -/
theorem zeta_rat_equiv {q m : Nat} (hq : 0 < q) (s : Rat) (hs : InChart q m s)
    (hdom : AboveOne (Real.ofRat s)) :
    (zeta (Real.ofRat s) hdom).preferred.Equiv (raw q m hq s) := by
  let x := Real.ofRat s
  have hconst (n : Nat) : (domainReal x hdom).compute n = ⟨s,s⟩ := rfl
  have ht := domainReal_inChart x hdom 0
  rw [hconst] at ht
  have hc : InChart (chartQ x hdom) (chartM x hdom) s := ⟨ht.1,ht.2.2⟩
  have he : (domainReal x hdom).preferred.Equiv (RealRaw.ofRat s) :=
    RealRaw.equiv_symm (RealRaw.schedule_equiv x.preferred x.valid (domainSchedule x hdom))
  have h1 := atReal_equiv_raw (Nat.zero_lt_succ _) (domainReal x hdom) (domainReal_inChart x hdom) s hc he
  exact RealRaw.equiv_trans (zeta x hdom).valid (raw_valid (Nat.zero_lt_succ _) hc) (raw_valid hq hs)
    h1 (raw_chart_equiv (Nat.zero_lt_succ _) hq hc hs)

theorem integer_inChart (p : Nat) : InChart 1 p ((p : Rat)+2) := by
  have h := Rat.natCast_nonneg (a := p)
  constructor <;> grind [InChart, Rat.div_def]

theorem integer_aboveOne (p : Nat) : AboveOne (Real.ofRat ((p : Rat)+2)) := by
  refine ⟨0,?_⟩
  change 1 < (p : Rat)+2
  have h := Rat.natCast_nonneg (a := p)
  grind

/-- Every old integer zeta value is recovered by the new real-domain function. -/
theorem zeta_integer_equiv (p : Nat) :
    (zeta (Real.ofRat ((p : Rat)+2)) (integer_aboveOne p)).preferred.Equiv
      (DirichletSeries.zetaNatRaw (p+2)) :=
  RealRaw.equiv_trans (zeta _ _).valid (raw_valid (by decide : 0 < 1) (integer_inChart p))
    (DirichletSeries.zetaNatRaw_validCompute (p+2) (by omega))
    (zeta_rat_equiv (by decide) _ (integer_inChart p) (integer_aboveOne p))
    (raw_integer_equiv (by decide) p (integer_inChart p))

/-- In particular, this is the same zeta(3) already used as the Apéry target. -/
theorem zeta_three_equiv :
    (zeta (Real.ofRat 3) (by exact ⟨0, by decide⟩)).preferred.Equiv
      (DirichletSeries.zetaNatRaw 3) := by
  have h := zeta_integer_equiv 1
  have he : ((1 : Nat) : Rat)+2=3 := by grind
  simpa only [he] using h

end ComputableAnalysis.ZetaReal
