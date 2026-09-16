import ComputableAnalysis.Calculus

/-! A fixed-stage reciprocal for interval programs bounded away from zero.
There is no search for a positive interval hidden in the runtime. -/
namespace ComputableAnalysis
namespace PositiveIntervalInverse

theorem one_div_antitone {a b : Rat} (ha : 0 <a) (hab : a <=b) : 1/b <=1/a := by
  have hb : 0 <b := by grind
  have hca:=Rat.mul_inv_cancel a (Rat.ne_of_gt ha)
  have hcb:=Rat.mul_inv_cancel b (Rat.ne_of_gt hb)
  apply Rat.le_of_mul_le_mul_right (c:=a*b)
  · simp only [Rat.div_def,Rat.one_mul]
    have hL : b⁻¹*(a*b)=a := by grind [Rat.mul_assoc,Rat.mul_comm]
    have hR : a⁻¹*(a*b)=b := by grind [Rat.mul_assoc,Rat.mul_comm]
    rw [hL,hR]
    exact hab
  · exact Rat.mul_pos ha hb

def raw (X : RealRaw) : RealRaw where
  compute := fun n=>{lo:=1/(X.compute n).hi,hi:=1/(X.compute n).lo}

theorem width (X : RealRaw) (hX : X.Valid)
    (lower : ∀ n, (1 : Rat)/4 <=(X.compute n).lo) (n : Nat) :
    ((raw X).compute n).width <=16*(X.compute n).width := by
  let a:=(X.compute n).lo; let b:=(X.compute n).hi
  have ha : (1 : Rat)/4 <=a:=lower n
  have hab : a <=b:=RealRaw.interval_order_of_valid X hX n
  have ha0 : 0 <a := by simp only [Rat.div_def] at ha; grind
  have hb0 : 0 <b := by grind
  have h1:=Rat.mul_le_mul_of_nonneg_right ha (Rat.le_of_lt hb0)
  have hb : (1 : Rat)/4 <=b := by grind
  have h2:=Rat.mul_le_mul_of_nonneg_left hb (by decide +kernel : (0 : Rat) <=1/4)
  have hca:=Rat.mul_inv_cancel a (Rat.ne_of_gt ha0)
  have hcb:=Rat.mul_inv_cancel b (Rat.ne_of_gt hb0)
  have hi0 : 0 <=1/a-1/b := by have h:=one_div_antitone ha0 hab; grind
  have hid : (1/a-1/b)*(a*b)=b-a := by simp only [Rat.div_def,Rat.one_mul]; grind
  have hab16 : (1 : Rat)/16 <=a*b := by simp only [Rat.div_def] at h1 h2 ⊢; grind
  have hm:=Rat.mul_le_mul_of_nonneg_left hab16 hi0
  rw [hid] at hm
  change 1/a-1/b <=16*(b-a)
  simp only [Rat.div_def] at hm
  grind

theorem valid (X : RealRaw) (hX : X.Valid)
    (lower : ∀ n, (1 : Rat)/4 <=(X.compute n).lo) : (raw X).Valid := by
  have pos (n : Nat) : 0 <(X.compute n).lo := by
    have h:=lower n; simp only [Rat.div_def] at h; grind
  have hipos (n : Nat) : 0 <(X.compute n).hi :=
    by have hp:=pos n; have ho:=RealRaw.interval_order_of_valid X hX n; grind
  have ord (n : Nat) : 1/(X.compute n).hi <=1/(X.compute n).lo :=
    one_div_antitone (pos n) (RealRaw.interval_order_of_valid X hX n)
  refine ⟨?_,?_,?_⟩
  · intro n
    have h:=ord n
    change 0 <=1/(X.compute n).lo-1/(X.compute n).hi
    grind
  · intro n m hnm
    have h:=hX.2.1 n m hnm
    exact ⟨one_div_antitone (hipos m) h.2.2,ord m,one_div_antitone (pos n) h.1⟩
  · intro eps
    let eta : QPos:=⟨eps.val/16,by rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨N,hN⟩:=hX.2.2 eta
    refine ⟨N,fun n hn=>?_⟩
    have hw:=width X hX lower n
    have hs:=hN n hn
    dsimp [eta] at hs
    simp only [Rat.div_def] at hs
    grind

end PositiveIntervalInverse
end ComputableAnalysis
