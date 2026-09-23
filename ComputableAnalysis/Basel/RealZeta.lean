import ComputableAnalysis.Basel.Primes
import ComputableAnalysis.ZetaReal.Compatibility

namespace ComputableAnalysis.Basel
open DirichletSeries

/-- The older natural-exponent and reciprocal-square evaluators have
identical stage boxes at exponent two. -/
theorem zetaNatTwo_compute (n : Nat) : (zetaNatRaw 2).compute n=zetaTwoRaw.compute n := by
  have hp (m : Nat) : zetaNatPartial 2 m=zetaTwoPartial m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [zetaNatPartial, zetaTwoPartial, ih]
      have ht : zetaNatTerm 2 m=zetaTwoTerm m := by
        simp only [zetaNatTerm, zetaTwoTerm, Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
      rw [ht]
  change ({lo:=zetaNatPartial 2 n, hi:=zetaNatPartial 2 n+zetaNatTailBound n} : QInterval)=_
  rw [hp]; rfl

theorem zetaNatTwo_equiv : (zetaNatRaw 2).Equiv zetaTwoRaw := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [zetaNatTwo_compute]
  have h := zetaTwoInterval_ordered n
  exact ⟨h,h⟩

/-- Basel also holds for the public zeta function on represented real inputs. -/
theorem real_zeta_two_equiv_piSquaredOverSix :
    (ZetaReal.zeta (Real.ofRat 2) (by exact ⟨0,by decide⟩)).preferred.Equiv
      geometricPiSquaredOverSixRaw := by
  have hi := ZetaReal.zeta_integer_equiv 0
  have hzero : ((0:Nat):Rat)+2=2 := by grind only
  simp only [hzero] at hi
  have hz := RealRaw.equiv_trans (ZetaReal.zeta _ _).valid
    (zetaNatRaw_validCompute 2 (by omega)) baselSeriesRaw_valid hi zetaNatTwo_equiv
  exact RealRaw.equiv_trans (ZetaReal.zeta _ _).valid baselSeriesRaw_valid
    geometricPiSquaredOverSixRaw_valid hz eulerBasel

end ComputableAnalysis.Basel
