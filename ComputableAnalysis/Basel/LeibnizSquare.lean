import ComputableAnalysis.Basel.FiniteSums

/-! Exact square and triangular identities for finite Leibniz sums. -/
namespace ComputableAnalysis.Basel
open FormalPowerSeries
open Series (alternatingSign partialSum leibnizTerm)

abbrev b := leibnizTerm
abbrev a (k : Nat) : Rat := alternatingSign k * b k
def H (n : Nat) : Rat := sumBelow b n
def B (n : Nat) : Rat := partialSum b n
def M (n : Nat) : Rat := sumBelow (fun k => b k*b k) n
def T (n : Nat) : Rat := sumBelow (fun k => alternatingSign k * H (k+1) / ((k+1:Nat):Rat)) n
/-- Average of the last `d` odd reciprocals in the first `n` terms. -/
def G (n d : Nat) : Rat := (H n-H (n-d)) / (d:Rat)

 theorem b_cancel (k : Nat) : (2*(k:Rat)+1)*b k=1 := by
  have hk : 0≤(k:Rat) := Rat.natCast_nonneg
  have hd : 2*(k:Rat)+1≠0 := by grind only
  simpa [b, leibnizTerm, Rat.div_def] using Rat.mul_inv_cancel (2*(k:Rat)+1) hd

 theorem b_pair (i j : Nat) :
    b i*b j = (b i+b j) / (2*((i+j+1:Nat):Rat)) := by
  have hi := b_cancel i
  have hj := b_cancel j
  have hn : 0<((i+j+1:Nat):Rat) := Rat.natCast_pos.mpr (by omega)
  have hd : (2*((i+j+1:Nat):Rat))≠0 := by grind only
  have hc := Rat.mul_inv_cancel (2*((i+j+1:Nat):Rat)) hd
  have he : b i*b j*(2*((i+j+1:Nat):Rat))=b i+b j := by
    have hi' := congrArg (fun x=>x*b j) hi
    have hj' := congrArg (fun x=>x*b i) hj
    simp only [Rat.natCast_add] at *
    grind only
  have := congrArg (fun x=>x*(2*((i+j+1:Nat):Rat))⁻¹) he
  grind only [Rat.div_def]

 theorem b_difference (i d : Nat) (hd : 0<d) :
    2*(b i*b (i+d)) = (b i-b (i+d))/(d:Rat) := by
  have hi := b_cancel i
  have hj := b_cancel (i+d)
  have hn : (d:Rat)≠0 := by have := Rat.natCast_pos.mpr hd; grind only
  have hc := Rat.mul_inv_cancel (d:Rat) hn
  have hi' := congrArg (fun x=>x*b (i+d)) hi
  have hj' := congrArg (fun x=>x*b i) hj
  have he : (2*(b i*b (i+d)))*(d:Rat)=b i-b (i+d) := by
    simp only [Rat.natCast_add] at hj'
    grind only
  have := congrArg (fun x=>x*(d:Rat)⁻¹) he
  grind only [Rat.div_def]

 theorem antidiagonal (d : Nat) :
    sumBelow (fun i=>a i*a (d-i)) (d+1) = alternatingSign d * H (d+1) / ((d+1:Nat):Rat) := by
  have ht : sumBelow (fun i=>a i*a (d-i)) (d+1) =
    sumBelow (fun i=> (alternatingSign d / (2*((d+1:Nat):Rat))) * (b i+b (d-i))) (d+1) := by
    apply sumBelow_congr; intro i hi
    have hs := Series.alternatingSign_add i (d-i)
    rw [show i+(d-i)=d by omega] at hs
    have hp := b_pair i (d-i)
    rw [show i+(d-i)+1=d+1 by omega] at hp
    change (alternatingSign i*b i)*(alternatingSign (d-i)*b (d-i))=_
    have := congrArg (fun x=>alternatingSign d*x) hp
    grind only [Rat.div_def]
  rw [ht, sumBelow_mul, sumBelow_add]
  have hr : sumBelow (fun i=>b (d-i)) (d+1)=H (d+1) := by
    simpa only [H, show d+1-1=d by omega] using sum_reverse b (d+1)
  rw [hr]
  change alternatingSign d/(2*((d+1:Nat):Rat)) * (H (d+1)+H (d+1)) = _
  rw [Rat.div_def, Rat.inv_mul_rev]
  grind only [Rat.div_def]

 theorem triangle_rows (n : Nat) : T n = sumBelow (fun i=>a i*B (n-i)) n := by
  have ht := sum_triangle (fun i j=>a i*a j) n
  have ha : sumBelow (fun d=>sumBelow (fun i=>a i*a (d-i)) (d+1)) n=T n := by
    apply sumBelow_congr; intro d _; exact antidiagonal d
  rw [ha] at ht
  rw [← ht]
  apply sumBelow_congr; intro i _
  rw [sumBelow_mul, sum_signed]; rfl

 theorem diagonal (n d : Nat) (hd : 0<d) (hdn : d≤n) :
    2*sumBelow (fun i=>a i*a (i+d)) (n-d) =
    alternatingSign d * ((H d)/ (d:Rat) - G n d) := by
  have he : sumBelow (fun i=>a i*a (i+d)) (n-d) =
    sumBelow (fun i=>alternatingSign d*(b i*b (i+d))) (n-d) := by
    apply sumBelow_congr; intro i _
    have := Series.alternatingSign_add i d
    have hs := sign_sq i
    have hc := congrArg (fun x=>x*(b i*b (i+d))*alternatingSign d) hs
    dsimp [a]; grind only
  rw [he, sumBelow_mul]
  have ht : sumBelow (fun i=>2*(b i*b (i+d))) (n-d)=
    sumBelow (fun i=>(b i-b (i+d))/(d:Rat)) (n-d) := by
    apply sumBelow_congr; intro i _; exact b_difference i d hd
  rw [sumBelow_mul] at ht
  have hs : sumBelow (fun i=>(b i-b (i+d))/(d:Rat)) (n-d)=
    (H (n-d)- (H n-H d))/(d:Rat) := by
    simp only [Rat.div_def]
    have heq : sumBelow (fun i=>(b i-b (i+d))*(d:Rat)⁻¹) (n-d) =
      (d:Rat)⁻¹ * sumBelow (fun i=>b i-b (i+d)) (n-d) := by
      rw [← sumBelow_mul]; apply sumBelow_congr; intro i _; grind only
    rw [heq, sum_sub]
    have hb := sum_block b d (n-d)
    rw [show d+(n-d)=n by omega] at hb
    have hr : sumBelow (fun i=>b (i+d)) (n-d)=sumBelow (fun i=>b (d+i)) (n-d) := by
      apply sumBelow_congr; intro i _; congr 1; omega
    rw [hr]; dsimp [H] at *; grind only
  rw [hs] at ht
  have := congrArg (fun x=>alternatingSign d*x) ht
  dsimp [G]; grind only [Rat.div_def]

theorem square_identity (n : Nat) :
    B n*B n+T n-M n = sumBelow (fun k=>alternatingSign k*G n (k+1)) n := by
  have hs := sum_square (fun i j=>a i*a j) n
  have hleft : sumBelow (fun i=>sumBelow (fun j=>a i*a j) n) n=B n*B n := by
    simp only [sumBelow_mul]
    have he : sumBelow (fun i=>a i*sumBelow a n) n =
      sumBelow a n*sumBelow a n := by
      rw [← sumBelow_mul]; apply sumBelow_congr; intro i _; grind only
    rw [he, sum_signed]; rfl
  have hmain : sumBelow (fun i=>a i*a i) n=M n := by
    apply sumBelow_congr; intro i _
    have := congrArg (fun x=>x*(b i*b i)) (sign_sq i)
    dsimp [a]; grind only
  have hoff : sumBelow (fun i=>sumBelow (fun j=>a i*a (i+1+j)+a (i+1+j)*a i) (n-1-i)) n =
    sumBelow (fun d=>2*sumBelow (fun i=>a i*a (i+(d+1))) (n-(d+1))) n := by
    have ht := triangle_swap (fun i j=>a i*a (i+1+j)+a (i+1+j)*a i) (n-1)
    have hz (f : Nat→Rat) (hf : f (n-1)=0) : sumBelow f n=sumBelow f (n-1) := by
      cases n with
      | zero => rfl
      | succ n => simp only [Nat.add_sub_cancel, sumBelow_succ] at *; grind only
    have hl := hz (fun i=>sumBelow (fun j=>a i*a (i+1+j)+a (i+1+j)*a i) (n-1-i)) (by simp)
    have hr := hz (fun d=>sumBelow (fun i=>a i*a (i+1+d)+a (i+1+d)*a i) (n-1-d)) (by simp)
    rw [hl, ht, ← hr]
    apply sumBelow_congr; intro d _
    rw [show n-(d+1)=n-1-d by omega, ← sumBelow_mul]
    apply sumBelow_congr; intro i _
    rw [show i+(d+1)=i+1+d by omega]; grind only
  rw [hleft, hmain, hoff] at hs
  have hd : sumBelow (fun d=>2*sumBelow (fun i=>a i*a (i+(d+1))) (n-(d+1))) n =
    sumBelow (fun d=> -alternatingSign d*(H (d+1)/((d+1:Nat):Rat)-G n (d+1))) n := by
    apply sumBelow_congr; intro d hd
    rw [diagonal n (d+1) (by omega) (by omega), sign_succ]
  rw [hd] at hs
  have he : sumBelow (fun d=> -alternatingSign d*(H (d+1)/((d+1:Nat):Rat)-G n (d+1))) n =
    sumBelow (fun d=>alternatingSign d*G n (d+1)) n-T n := by
    dsimp only [T]; rw [← sum_sub]; apply sumBelow_congr; intro d _; grind only [Rat.div_def]
  rw [he] at hs; grind only

end ComputableAnalysis.Basel
