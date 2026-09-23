import ComputableAnalysis.Basel.EulerBounds
import ComputableAnalysis.Basel

/-! Rationality forced by an exhaustive finite prime list, proved by finite
Euler sieving and its rational error budget. -/
namespace ComputableAnalysis.Basel
open DirichletSeries

/-- Under an exhaustive finite list of distinct primes, zeta at two is the
rational reciprocal of the finite Euler coefficient. -/
theorem zetaTwo_equiv_finiteEulerProduct {ps : List Nat}
    (hps : ∀p, p∈ps → BasicPrime p) (hnd : ps.Nodup)
    (hall : ∀p, BasicPrime p → p∈ps) :
    zetaTwoRaw.Equiv (RealRaw.ofRat (1/EulerSieve.coefficient ps)) := by
  have hc := (EulerSieve.coefficient_bounds hps).1
  apply equiv_of_close_lower_refinements baselSeriesRaw_valid (RealRaw.ofRat_valid _)
  intro stage eps
  let scaled : QPos := ⟨eps.val*EulerSieve.coefficient ps, Rat.mul_pos eps.property hc⟩
  have hs : ShrinksToZero (fun n=>(EulerSieve.budget ps:Rat)/((n+1:Nat):Rat)) :=
    shrinksToZero_of_natOverSuccBound (fun _=>Rat.le_refl)
  obtain ⟨N,hN⟩ := hs scaled
  let n := N+stage+1
  have hn : 0<n := by dsimp [n]; omega
  refine ⟨n,stage,by dsimp [n]; omega,Nat.le_refl _,?_⟩
  change qabs (zetaTwoPartial n-1/EulerSieve.coefficient ps)≤eps.val
  have h := EulerSieve.sieve_error hps hnd n
  rw [EulerSieve.sieve_all_primes hps hall n hn] at h
  have hb := hN n (by dsimp [n]; omega)
  have hnear : qabs (1-EulerSieve.coefficient ps*zetaTwoPartial n)≤eps.val*EulerSieve.coefficient ps :=
    Rat.le_trans h hb
  apply (Rat.le_of_mul_le_mul_right · hc)
  have he : (zetaTwoPartial n-1/EulerSieve.coefficient ps)*EulerSieve.coefficient ps=
      -(1-EulerSieve.coefficient ps*zetaTwoPartial n) := by
    have := Rat.mul_inv_cancel (EulerSieve.coefficient ps) (Rat.ne_of_gt hc)
    grind only [Rat.div_def]
  have ha := congrArg qabs he
  rw [qabs_mul, qabs_eq_self_of_nonneg (Rat.le_of_lt hc), qabs_neg] at ha
  rw [ha]; exact hnear

/-- The Euler-product route from irrationality of zeta at two to a prime
above every finite bound. The Euclidean infinitude theorem is not used. -/
theorem prime_unbounded_of_zetaTwo_irrational (h : zetaTwoRaw.Irrational) (bound : Nat) :
    ∃p, BasicPrime p ∧ bound<p := by
  classical
  apply Classical.byContradiction; intro hn
  let ps := (List.range (bound+1)).filter (fun p=>decide (BasicPrime p))
  have hmem (p : Nat) : p∈ps ↔ p<bound+1 ∧ BasicPrime p := by simp [ps]
  have hps : ∀p, p∈ps → BasicPrime p := by intro p hp; exact ((hmem p).mp hp).2
  have hall : ∀p, BasicPrime p → p∈ps := by
    intro p hp; apply (hmem p).mpr
    refine ⟨?_,hp⟩
    apply Classical.byContradiction; intro hlt
    exact hn ⟨p,hp,by omega⟩
  have hnd : ps.Nodup := List.Nodup.sublist List.filter_sublist List.nodup_range
  exact h _ (zetaTwo_equiv_finiteEulerProduct hps hnd hall)

end ComputableAnalysis.Basel
