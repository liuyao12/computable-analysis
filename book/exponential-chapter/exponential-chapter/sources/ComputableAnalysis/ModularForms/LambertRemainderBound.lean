import ComputableAnalysis.ModularForms.LambertDifference

/-! Quantitative bounds for the actual Lambert first-order remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem nomeGeometricSum_bound (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) : Small (nomeGeometricSum z r) 4 := by
  have h := ScalarSeries.value_bound (LocalODE.power z.val)
    (LocalODE.power_valid _ z.property) 1 (2*r) (by decide)
    (Rat.mul_nonneg (by decide) hr) hlocal (fun n => by
      apply (LocalODE.power_small z.val z.property r hr hz n).mono
      have hp := Rat.pow_nonneg (n := n) (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hr)
      grind only)
  rw [show (4:Rat)*1=4 by decide +kernel] at h
  exact h

theorem lambertFactor_remainder_bound (z w : Scalar) (r s H : Rat)
    (hr : 0≤r) (hs : 0≤s) (hH : 0≤H)
    (hrlocal : 2*r≤(1:Rat)/2) (hslocal : 2*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (hd : Small (sub w.val z.val) H) :
    Small (sub (sub (lambertFactor w s) (lambertFactor z r))
      (mul (sub w.val z.val) (mul (nomeGeometricSum z r) (nomeGeometricSum z r))))
      (1024*H^2) := by
  have va := nomeGeometricSum_valid z r hr hrlocal hz
  have vb := nomeGeometricSum_valid w s hs hslocal hw
  have vd := sub_valid w.property z.property
  have ha := nomeGeometricSum_bound z r hr hrlocal hz
  have hb := nomeGeometricSum_bound w s hs hslocal hw
  have haa := Small.mul va va (show (0:Rat)≤4 by decide) (by decide) ha ha
  rw [show (2:Rat)*4*4=32 by decide +kernel] at haa
  have hab := Small.mul (mul_valid va va) vb (show (0:Rat)≤32 by decide) (by decide) haa hb
  rw [show (2:Rat)*32*4=256 by decide +kernel] at hab
  have hdd := Small.mul vd vd hH hH hd hd
  have h := Small.mul (mul_valid vd vd) (mul_valid (mul_valid va va) vb)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) hH)
    (show (0:Rat)≤256 by decide) hdd hab
  have he : (2:Rat)*(2*H*H)*256=1024*H^2 := by
    rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_zero]
    grind only
  rw [he] at h
  exact Small.congr (mul_valid (mul_valid vd vd) (mul_valid (mul_valid va va) vb))
    (sub_valid (sub_valid (lambertFactor_valid w s hs hslocal hw)
      (lambertFactor_valid z r hr hrlocal hz)) (mul_valid vd (mul_valid va va)))
    (equiv_symm (lambertFactor_quadratic_identity z w r s hr hs hrlocal hslocal hz hw)) h

end ComputableAnalysis.ModularForms
