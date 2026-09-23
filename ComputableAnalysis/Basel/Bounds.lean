import ComputableAnalysis.Basel.LeibnizSquare

/-! Explicit rational errors for the finite square rearrangement. -/
namespace ComputableAnalysis.Basel
open FormalPowerSeries
open Series (alternatingSign partialSum)

theorem b_nonneg (k : Nat) : 0≤b k := Series.leibnizTerm_nonneg k

theorem b_antitone {i j : Nat} (h : i≤j) : b j≤b i := by
  induction h with
  | refl => exact Rat.le_refl
  | step h ih => exact Rat.le_trans (Series.leibnizTerm_decreasing _) ih

theorem H_nonneg (n : Nat) : 0≤H n := sum_nonneg (fun k _=>b_nonneg k)

theorem H_mono {i j : Nat} (h : i≤j) : H i≤H j := by
  have he := sum_block b i (j-i)
  rw [show i+(j-i)=j by omega] at he
  have := sum_nonneg (f:=fun k=>b (i+k)) (n:=j-i) (fun k _=>b_nonneg _)
  dsimp [H]; grind only

theorem H_tail_bound (n d : Nat) (hd : d≤n) :
    H n-H (n-d) ≤ (d:Rat)*b (n-d) := by
  have hb := sum_block b (n-d) d
  rw [show n-d+d=n by omega] at hb
  have he := sum_le (n:=d) (f:=fun k=>b (n-d+k)) (g:=fun _=>b (n-d))
    (fun k _=>b_antitone (by omega))
  rw [sum_const] at he
  dsimp [H]; grind only

theorem G_nonneg (n d : Nat) : 0≤G n d := by
  have h := H_mono (show n-d≤n by omega)
  cases d with
  | zero => simp [G, Rat.div_def]
  | succ d =>
    dsimp [G]; rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind only) (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (by omega))))

theorem G_step (n d : Nat) (hd : 0<d) (hdn : d<n) : G n d≤G n (d+1) := by
  have htail := H_tail_bound n d (by omega)
  have hterm := b_antitone (show n-(d+1)≤n-d by omega)
  have he : H (n-d)=H (n-(d+1))+b (n-(d+1)) := by
    dsimp [H]; rw [show n-d=(n-(d+1))+1 by omega, sumBelow_succ]
  have dp : 0<(d:Rat) := Rat.natCast_pos.mpr hd
  have ep : 0<((d+1:Nat):Rat) := Rat.natCast_pos.mpr (by omega)
  have dc := Rat.mul_inv_cancel (d:Rat) (by grind only)
  have ec := Rat.mul_inv_cancel ((d+1:Nat):Rat) (by grind only)
  have hmul := Rat.mul_le_mul_of_nonneg_left hterm (Rat.le_of_lt dp)
  apply (Rat.le_of_mul_le_mul_right · dp)
  apply (Rat.le_of_mul_le_mul_right · ep)
  dsimp [G]
  have hdce := congrArg (fun x=>x*(H n-H (n-d))*((d+1:Nat):Rat)) dc
  have hece := congrArg (fun x=>x*(H n-H (n-(d+1)))*(d:Rat)) ec
  have he' := congrArg (fun x=>x*(d:Rat)) he
  simp only [Rat.natCast_add] at *
  grind only [Rat.div_def]

theorem sign_abs (n : Nat) : qabs (alternatingSign n)=1 := by
  unfold alternatingSign; split <;> simp [qabs] <;> grind only

theorem square_triangle_error (n : Nat) (hn : 0<n) :
    qabs (B n*B n+T n-M n) ≤ H n/(n:Rat) := by
  rw [square_identity, sum_signed]
  have h := alternating_increasing (fun k=>G n (k+1)) (n-1)
    (fun k _=>G_nonneg n (k+1))
    (fun k hk=>G_step n (k+1) (by omega) (by omega))
  rw [show n-1+1=n by omega] at h
  have he : G n n=H n/(n:Rat) := by simp [G, H]; grind only [Rat.div_def]
  rw [he] at h
  have hab : qabs (alternatingSign (n-1)*partialSum (fun k=>G n (k+1)) n)=
      qabs (partialSum (fun k=>G n (k+1)) n) := by
    rw [qabs_mul, sign_abs]; grind only
  have ha : qabs (alternatingSign (n-1)*partialSum (fun k=>G n (k+1)) n) ≤ H n/(n:Rat) := by
    rw [qabs_eq_self_of_nonneg h.1]; exact h.2
  rw [hab] at ha; exact ha

theorem B_tail (i j : Nat) (hi : i≤j) : qabs (B j-B i)≤b i := by
  have he := Series.partialSum_add_block b i (j-i)
  rw [show i+(j-i)=j by omega] at he
  have h := alternating_decreasing (fun k=>b (i+k)) (j-i)
    (fun k=>b_nonneg _) (fun k=>b_antitone (by omega))
  have hx : B j-B i=alternatingSign i*partialSum (fun k=>b (i+k)) (j-i) := by
    dsimp [B]; grind only
  rw [hx, qabs_mul, sign_abs, qabs_eq_self_of_nonneg h.1]
  simp only [Nat.add_zero] at h
  grind only

theorem triangle_square_error (n : Nat) (hn : 0<n) :
    qabs (B n*B n-T n) ≤ H n/(n:Rat) := by
  have he : B n*B n-T n=sumBelow (fun i=>a i*(B n-B (n-i))) n := by
    rw [triangle_rows]
    have ha : sumBelow (fun i=>a i*B n) n=B n*B n := by
      have hm := sumBelow_mul (B n) a n
      rw [sum_signed] at hm
      have hc : sumBelow (fun i=>a i*B n) n=sumBelow (fun i=>B n*a i) n := by
        apply sumBelow_congr; intro i _; grind only
      rw [hc, hm]; rfl
    rw [← ha, ← sum_sub]
    apply sumBelow_congr; intro i _; grind only
  rw [he]
  have ha := sum_abs (fun i=>a i*(B n-B (n-i))) n
  have hb : sumBelow (fun i=>qabs (a i*(B n-B (n-i)))) n ≤
      sumBelow (fun i=>b i*b (n-i)) n := by
    apply sum_le; intro i hi
    rw [qabs_mul, show qabs (a i)=b i by rw [a, qabs_mul, sign_abs, qabs_eq_self_of_nonneg (b_nonneg i)]; grind only]
    exact Rat.mul_le_mul_of_nonneg_left (B_tail (n-i) n (by omega)) (b_nonneg i)
  have hc : sumBelow (fun i=>b i*b (n-i)) n ≤ H n/(n:Rat) := by
    have hp : sumBelow (fun i=>b i*b (n-i)) n =
      (H n + sumBelow (fun i=>b (n-i)) n)/(2*((n+1:Nat):Rat)) := by
      have hh : sumBelow (fun i=>b i*b (n-i)) n =
          sumBelow (fun i=>(2*((n+1:Nat):Rat))⁻¹*(b i+b (n-i))) n := by
        apply sumBelow_congr; intro i hi
        have h := b_pair i (n-i)
        rw [show i+(n-i)+1=n+1 by omega] at h
        grind only [Rat.div_def]
      rw [hh, sumBelow_mul, sumBelow_add]; dsimp [H]; grind only [Rat.div_def]
    have ht : sumBelow (fun i=>b (n-i)) n ≤ H n := by
      dsimp only [H]
      rw [← sum_reverse b n]
      apply sum_le; intro i hi; exact b_antitone (by omega)
    rw [hp]
    have np : 0<(n:Rat) := Rat.natCast_pos.mpr hn
    have ep : 0<2*((n+1:Nat):Rat) := by have := Rat.natCast_pos.mpr (Nat.succ_pos n); grind only
    have nc := Rat.mul_inv_cancel (n:Rat) (by grind only)
    have ec := Rat.mul_inv_cancel (2*((n+1:Nat):Rat)) (by grind only)
    apply (Rat.le_of_mul_le_mul_right · np)
    apply (Rat.le_of_mul_le_mul_right · ep)
    have nc' := congrArg (fun x=>x*H n*(2*((n+1:Nat):Rat))) nc
    have ec' := congrArg (fun x=>x*(H n+sumBelow (fun i=>b (n-i)) n)*(n:Rat)) ec
    have ht' := Rat.mul_le_mul_of_nonneg_right ht (Rat.le_of_lt np)
    have := H_nonneg n
    simp only [Rat.natCast_add] at *
    grind only [Rat.div_def]
  exact Rat.le_trans ha (Rat.le_trans hb hc)

/-- The core Basel estimate, involving only finite rational sums. -/
theorem leibniz_square_error (n : Nat) (hn : 0<n) :
    qabs (2*(B n*B n)-M n) ≤ 2*H n/(n:Rat) := by
  have hs := square_triangle_error n hn
  have ht := triangle_square_error n hn
  have ha := qabs_add_le (B n*B n+T n-M n) (B n*B n-T n)
  rw [show B n*B n+T n-M n+(B n*B n-T n)=2*(B n*B n)-M n by grind only] at ha
  grind only [Rat.div_def]

end ComputableAnalysis.Basel
