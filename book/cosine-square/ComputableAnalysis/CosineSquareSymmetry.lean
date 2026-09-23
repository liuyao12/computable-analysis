import ComputableAnalysis.CosineSquareData

/-! Reflection and the circle identity identify the independently valid
rectangle program. This route does not use the squared-cosine FTC proof. -/
namespace ComputableAnalysis.CosineSquare
open ClosedArctanInverse ClockTrigonometry MonotoneAverage IntervalSelections

theorem left_reflection (f : Rat → Rat) (a b : Rat) (n : Nat) :
    left (fun x=>f (1-x)) a b n=right f (1-b) (1-a) n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [left,right,ih]
    rw [show 1-(a+b)/2=((1-b)+(1-a))/2 by simp only [Rat.div_def];grind]
    rw [Rat.add_comm]

theorem left_constant (v a b : Rat) (n : Nat) : left (fun _=>v) a b n=v := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [left,ih,Rat.div_def];grind

theorem reflected_square_error (t : Rat) (ht : Unit t) (q : Nat) :
    qabs (sample t q+sample (1-t) q-1) ≤ 472*meshRadius q := by
  have a:=ClockTrigonometry.sample_bounds (1-t) q
  have b:=ClockTrigonometry.sample_bounds t q
  have e:=square_error ⟨a.1,a.2.1⟩ ⟨b.2.2.1,b.2.2.2⟩
    (ClockTrigonometry.sample_complement ht q).1
  have hc:=ClockTrigonometry.sample_unit t q
  have he : sample t q+sample (1-t) q-1=c (1-t) q*c (1-t) q-s t q*s t q := by
    dsimp [sample];grind only
  rw [he]
  grind only

/-- A finite estimate obtained by pairing left cells with reflected right
cells. The only residuals are the endpoint rectangle gap and sample error. -/
theorem symmetry_sum_error (q : Nat) : qabs (sumSample q-1/2) ≤ 237*meshRadius q := by
  let f := fun t=>sample t q
  have hp:=perturbation (fun t=>f t+f (1-t)) (fun _=>1) (472*meshRadius q)
    (fun t ht=>reflected_square_error t ht q)
    (a:=0) (b:=1) ⟨by decide +kernel,by decide +kernel⟩ ⟨by decide +kernel,by decide +kernel⟩ q
  rw [left_add,left_reflection,left_constant] at hp
  simp only [show (1:Rat)-1=0 by decide +kernel,show (1:Rat)-0=1 by decide +kernel] at hp
  have hg:=gap f 0 1 q
  have h0:=sample_bounds 0 q
  have h1:=sample_bounds 1 q
  have hr:=Rat.le_of_lt (meshRadius_pos q)
  have hgap:=Rat.mul_le_mul_of_nonneg_left
    (show f 0-f 1≤1 by dsimp [f];grind only) hr
  have ho:=ordered f (sample_decreases q)
    (a:=0) (b:=1) ⟨by decide +kernel,by decide +kernel⟩ ⟨by decide +kernel,by decide +kernel⟩ (by decide +kernel) q
  have hn:=neg_qabs_le_self (left f 0 1 q+right f 0 1 q-1)
  have hpos:=self_le_qabs (left f 0 1 q+right f 0 1 q-1)
  change qabs (left f 0 1 q-1/2)≤237*meshRadius q
  apply qabs_le_of_neg_le_le <;> simp only [Rat.div_def] <;> grind only

theorem quarterIntegral_via_symmetry : quarterIntegral.Equiv (RealRaw.ofRat (1/2)) :=
  ClockTrigonometry.equiv_of_geometric_error quarterIntegral_valid (RealRaw.ofRat_valid _)
    sumSample (fun _=>1/2) sumSample_mem (rat_mem _) 237 symmetry_sum_error

/-- The normalized squared-cosine integral, by reflection and Pythagoras. -/
theorem integral_via_symmetry : integral.Equiv (RealRaw.ofRat (1/4)) := by
  exact normalize_value quarterIntegral_via_symmetry

end ComputableAnalysis.CosineSquare
