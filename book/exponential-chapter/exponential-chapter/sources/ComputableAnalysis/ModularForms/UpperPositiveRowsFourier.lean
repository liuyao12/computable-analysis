import ComputableAnalysis.ModularForms.NomeIntegerScaling
import ComputableAnalysis.ModularForms.UpperPositiveRowsLimits
import ComputableAnalysis.ModularForms.IntegerPowerQuarticFourier
import ComputableAnalysis.ModularForms.IntegerPowerSexticFourier

/-! Actual positive-row Fourier formulas at powers of the original nome. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Each actual quartic row has its Fourier formula at the corresponding original nome power. -/
theorem upperPositiveLatticeRowSum_quartic_nomePower (z : Scalar)
    (hz : InUpperHalfPlane z.val) (r : Rat) (hr : 0≤r)
    (hlocal : 32*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) (n : Nat) :
    (upperPositiveLatticeRowSum z hz 4 (by omega) n).val.Equiv
      (scaleRat (8/3) (mul (LocalODE.power geometricPiScalar.val 4)
        (polynomialNomeMomentSum (nomePowerScalar (nome.eval z hz) n) (nomePowerRadius r n) 3))) := by
  let w := integerScaleScalar z ((n+1:Nat):Int)
  have hw := integerScaleScalar_upper z hz ((n+1:Nat):Int) (by omega)
  let R := nomePowerRadius r n
  have hR : 0≤R := nomePowerRadius_nonneg r hr n
  have hbound : R≤2*r := nomePowerRadius_le r hr (by grind only) n
  have hguard : 16*R≤(1:Rat)/2 := by
    have hb := Rat.mul_le_mul_of_nonneg_left hbound (show (0:Rat)≤16 by decide +kernel)
    grind only
  have hratio : polynomialNomeMomentRatio R 3≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_three]
    exact hguard
  have hqw : Small (nome.eval w hw).val R := nome_integerScale_small z hz r hr hq n
  have hqp : Small (nomePowerScalar (nome.eval z hz) n).val R :=
    nomePowerScalar_small (nome.eval z hz) r hr hq n
  have vs := polynomialNomeMomentSum_valid (nome.eval w hw) R 3 hR hratio hqw
  have vp := polynomialNomeMomentSum_valid (nomePowerScalar (nome.eval z hz) n) R 3 hR hratio hqp
  have hm := polynomialNomeMomentSum_congr (nome.eval w hw)
    (nomePowerScalar (nome.eval z hz) n) R R 3 hR hR hratio hratio hqw hqp
    (nome_integerScale_power z hz (n+1) (by omega))
  exact equiv_trans (upperPositiveLatticeRowSum z hz 4 (by omega) n).property
    (scaleRat_valid (r := (8/3:Rat)) (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 4) vs))
    (scaleRat_valid (r := (8/3:Rat)) (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 4) vp))
    (integerReciprocalPowerRowSum_quartic_pi_fourier w hw R hR hguard hqw)
    (scaleRat_equiv (r := (8/3:Rat))
      (mul_equiv (LocalODE.power_valid _ geometricPiScalar.property 4)
        (LocalODE.power_valid _ geometricPiScalar.property 4) vs vp
        (equiv_refl _ (LocalODE.power_valid _ geometricPiScalar.property 4)) hm))

theorem upperPositiveLatticeRowSum_sextic_nomePower (z : Scalar)
    (hz : InUpperHalfPlane z.val) (r : Rat) (hr : 0≤r)
    (hlocal : 128*r≤(1:Rat)/2) (hq : Small (nome.eval z hz).val r) (n : Nat) :
    (upperPositiveLatticeRowSum z hz 6 (by omega) n).val.Equiv
      (scaleRat (-8/15) (mul (LocalODE.power geometricPiScalar.val 6)
        (polynomialNomeMomentSum (nomePowerScalar (nome.eval z hz) n) (nomePowerRadius r n) 5))) := by
  let w := integerScaleScalar z ((n+1:Nat):Int)
  have hw := integerScaleScalar_upper z hz ((n+1:Nat):Int) (by omega)
  let R := nomePowerRadius r n
  have hR : 0≤R := nomePowerRadius_nonneg r hr n
  have hbound : R≤2*r := nomePowerRadius_le r hr (by grind only) n
  have hguard : 64*R≤(1:Rat)/2 := by
    have hb := Rat.mul_le_mul_of_nonneg_left hbound (show (0:Rat)≤64 by decide +kernel)
    grind only
  have hratio : polynomialNomeMomentRatio R 5≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_five]
    exact hguard
  have hqw : Small (nome.eval w hw).val R := nome_integerScale_small z hz r hr hq n
  have hqp : Small (nomePowerScalar (nome.eval z hz) n).val R :=
    nomePowerScalar_small (nome.eval z hz) r hr hq n
  have vs := polynomialNomeMomentSum_valid (nome.eval w hw) R 5 hR hratio hqw
  have vp := polynomialNomeMomentSum_valid (nomePowerScalar (nome.eval z hz) n) R 5 hR hratio hqp
  have hm := polynomialNomeMomentSum_congr (nome.eval w hw)
    (nomePowerScalar (nome.eval z hz) n) R R 5 hR hR hratio hratio hqw hqp
    (nome_integerScale_power z hz (n+1) (by omega))
  exact equiv_trans (upperPositiveLatticeRowSum z hz 6 (by omega) n).property
    (scaleRat_valid (r := (-8/15:Rat)) (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 6) vs))
    (scaleRat_valid (r := (-8/15:Rat)) (mul_valid (LocalODE.power_valid _ geometricPiScalar.property 6) vp))
    (integerReciprocalPowerRowSum_sextic_pi_fourier w hw R hR hguard hqw)
    (scaleRat_equiv (r := (-8/15:Rat))
      (mul_equiv (LocalODE.power_valid _ geometricPiScalar.property 6)
        (LocalODE.power_valid _ geometricPiScalar.property 6) vs vp
        (equiv_refl _ (LocalODE.power_valid _ geometricPiScalar.property 6)) hm))

end ComputableAnalysis.ModularForms
