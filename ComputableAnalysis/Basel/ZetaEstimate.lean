import ComputableAnalysis.Basel.Bounds
import ComputableAnalysis.DirichletSeries

namespace ComputableAnalysis.Basel
open FormalPowerSeries DirichletSeries

 theorem zeta_even_odd (n : Nat) :
    zetaTwoPartial (2*n) = M n + (1/4)*zetaTwoPartial n := by
  induction n with
  | zero => simp [zetaTwoPartial, M]; grind only
  | succ n ih =>
    rw [show 2*(n+1)=(2*n+1)+1 by omega, zetaTwoPartial_succ, zetaTwoPartial_succ, ih,
      zetaTwoPartial_succ]
    have hm : M (n+1)=M n+b n*b n := sumBelow_succ _ n
    have ho : zetaTwoTerm (2*n)=b n*b n := by
      simp only [zetaTwoTerm, b, Series.leibnizTerm, Rat.div_def, Rat.one_mul, Rat.inv_mul_rev]
    have he : zetaTwoTerm (2*n+1)=(1/4)*zetaTwoTerm n := by
      simp only [zetaTwoTerm, Rat.natCast_add, Rat.natCast_mul]
      simp only [Rat.div_def, Rat.inv_mul_rev]
      grind only
    rw [hm, ho, he]; grind only

 theorem zeta_double_tail (n : Nat) (hn : 0<n) :
    0≤zetaTwoPartial (2*n)-zetaTwoPartial n ∧
      zetaTwoPartial (2*n)-zetaTwoPartial n≤1/(n:Rat) := by
  have he : zetaTwoPartial (n+n)=zetaTwoPartial n+zetaTwoFiniteTail n n := by
    have hb (k : Nat) : zetaTwoPartial (n+k)=zetaTwoPartial n+zetaTwoFiniteTail n k := by
      induction k with
      | zero => simp [zetaTwoFiniteTail]; grind only
      | succ k ih => rw [show n+(k+1)=(n+k)+1 by omega, zetaTwoPartial_succ, zetaTwoFiniteTail_succ, ih]; grind only
    exact hb n
  rw [show 2*n=n+n by omega, he]
  have := zetaTwoFiniteTail_nonneg n n
  have := zetaTwoFiniteTail_le_tailBound n hn n
  grind only

 theorem zeta_leibniz_error (n : Nat) (hn : 0<n) :
    qabs (zetaTwoPartial n-(8/3)*(B n*B n)) ≤ (8/3)*H n/(n:Rat)+(4/3)/(n:Rat) := by
  have hs := leibniz_square_error n hn
  have he := zeta_even_odd n
  have ht := zeta_double_tail n hn
  have hq := qabs_add_le (2*(B n*B n)-M n) (zetaTwoPartial (2*n)-zetaTwoPartial n)
  rw [qabs_eq_self_of_nonneg ht.1] at hq
  have id : zetaTwoPartial n-(8/3)*(B n*B n) =
      (-4/3)*((2*(B n*B n)-M n)+(zetaTwoPartial (2*n)-zetaTwoPartial n)) := by grind only
  rw [id, qabs_mul]
  have hp : qabs (-4/3:Rat)=4/3 := by simp [qabs]; grind only
  rw [hp]
  have hmul := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hq (by
    show qabs (2*(B n*B n)-M n)+(zetaTwoPartial (2*n)-zetaTwoPartial n) ≤ 2*H n/(n:Rat)+1/(n:Rat)
    grind only)) (show (0:Rat)≤4/3 by grind only [Rat.div_def])
  grind only [Rat.div_def]

 theorem H_square_bound (m : Nat) (hm : 0<m) : H (2*(m*m))≤3*(m:Rat) := by
  have hm1 : m≤m*m := by
    have h := Nat.mul_le_mul_left m (show 1≤m by omega)
    simpa using h
  have hmn : m≤2*(m*m) := by omega
  have he := sum_block b m (2*(m*m)-m)
  rw [show m+(2*(m*m)-m)=2*(m*m) by omega] at he
  have hhead : H m≤(m:Rat) := by
    have h := sum_le (n:=m) (f:=b) (g:=fun _=>1) (by
      intro k _; have h := b_antitone (show 0≤k by omega); have h0 : b 0=1 := by simp [b, Series.leibnizTerm, Rat.div_def]; grind only
      rw [h0] at h; exact h)
    rw [sum_const] at h; dsimp [H]; grind only
  have htail := sum_le (n:=2*(m*m)-m) (f:=fun k=>b (m+k)) (g:=fun _=>b m)
    (fun k _=>b_antitone (by omega))
  rw [sum_const] at htail
  have hnle : ((2*(m*m)-m:Nat):Rat)≤((2*(m*m):Nat):Rat) := Rat.natCast_le_natCast.mpr (by omega)
  have hmul := Rat.mul_le_mul_of_nonneg_right hnle (b_nonneg m)
  have hb : ((2*(m*m):Nat):Rat)*b m≤2*(m:Rat) := by
    have hc := b_cancel m
    have mp : 0<(m:Rat) := Rat.natCast_pos.mpr hm
    have hc' := congrArg (fun x=>x*(m:Rat)) hc
    have hbn := Rat.mul_nonneg (b_nonneg m) (show 0≤(m:Rat) by grind only)
    simp only [Rat.natCast_mul]
    grind only
  change sumBelow b (2*(m*m))≤3*(m:Rat)
  change sumBelow b m≤(m:Rat) at hhead
  grind only

/-- A square stage gives an explicit rational convergence schedule. -/
 theorem zeta_leibniz_square_budget (m : Nat) (hm : 0<m) :
    qabs (zetaTwoPartial (2*(m*m))-(8/3)*(B (2*(m*m))*B (2*(m*m)))) ≤ 16/(m:Rat) := by
  have mp : 0<(m:Rat) := Rat.natCast_pos.mpr hm
  have np : 0<2*(m*m) := Nat.mul_pos (by omega) (Nat.mul_pos hm hm)
  have h := zeta_leibniz_error (2*(m*m)) np
  have hh := H_square_bound m hm
  apply Rat.le_trans h
  have nn : 0<((2*(m*m):Nat):Rat) := Rat.natCast_pos.mpr np
  have mc := Rat.mul_inv_cancel (m:Rat) (by grind only)
  have nc := Rat.mul_inv_cancel ((2*(m*m):Nat):Rat) (by grind only)
  apply (Rat.le_of_mul_le_mul_right · nn)
  have nc' := congrArg (fun x=>x*((8/3)*H (2*(m*m))+(4/3))) nc
  have mc' := congrArg (fun x=>x*(32*(m:Rat))) mc
  have m1 : (1:Rat)≤(m:Rat) := by exact_mod_cast (show 1≤m by omega)
  simp only [Rat.natCast_mul] at *
  grind only [Rat.div_def]

end ComputableAnalysis.Basel
