import ComputableAnalysis.RealSecantDerivative
import ComputableAnalysis.ParametrizedCalculus

/-! Legacy finite secant estimates construct the shrinking all-pair condition
when their positive radii and continuous derivative-value extension are supplied. -/
namespace ComputableAnalysis
open RawLimit BracketDerivative BracketContinuity
set_option maxHeartbeats 3000000

theorem HasDerivativeOnInterval.toShrinkingSecantDerivative {F G : FunctionOnInterval}
    (D : HasDerivativeOnInterval F G) (positive : ∀ n, 0<D.stepPrecision n)
    {x d : RealRaw}
    (hG : HasContinuousAt (inDomainInterval G.lower G.upper) G.rationalValue x d) :
    RealSecantDerivative.HasDerivativeAt (inDomainInterval F.lower F.upper) F.rationalValue x d := by
  have same : inDomainInterval F.lower F.upper=inDomainInterval G.lower G.upper := by
    rw [D.same_lower,D.same_upper]
  have transport : ∀ A, Admissible (inDomainInterval F.lower F.upper) x A ↔
      Admissible (inDomainInterval G.lower G.upper) x A := fun _ => by rw [same]
  obtain ⟨A,hA⟩ := hG.2.2.2.1
  apply RealSecantDerivative.hasDerivative_iff_neighborhoods.mpr
  refine ⟨hG.1,hG.2.1,fun r _ => F.rationalValue_valid r,
    ⟨A,(transport A).mpr hA⟩,fun B hB => ⟨hG.2.1,?_⟩⟩
  have hBG := (transport B).mp hB
  have hg := (enclosureValue_iff (BracketContinuity.observations_antitone hB.2.1)).mp (hG.2.2.2.2 B hBG)
  intro m eps
  let tau : QPos := ⟨eps.val/4,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
  obtain ⟨N,hN⟩ := hg.2 m tau
  let p := tau.val.den+1
  have hp : 0<p := Nat.succ_pos _
  have htol : (precisionAtStage p).val≤tau.val := by
    simpa [precisionAtStage,p,Nat.ne_of_gt hp] using one_div_den_succ_le_of_pos tau.property
  let radius : QPos := ⟨1/((D.stepPrecision p:Nat):Rat),one_div_nat_pos (positive p)⟩
  obtain ⟨M,hM⟩ := hB.2.1.2.2 radius
  let K := max N M
  refine ⟨K,?_⟩
  rintro y ⟨a,b,ha,hab,hb,rfl⟩
  have mem := (hB.2.2.2 K).2
  have da := mem a ha (Rat.le_trans (Rat.le_of_lt hab) hb)
  have db := mem b (Rat.le_trans ha (Rat.le_of_lt hab)) hb
  have daG := (hBG.2.2.2 K).2 a ha (Rat.le_trans (Rat.le_of_lt hab) hb)
  have gd := hN (G.rationalValue a) (BracketContinuity.observations_antitone hB.2.1 N K
    (Nat.le_max_left _ _) _ ⟨a,ha,Rat.le_trans (Rat.le_of_lt hab) hb,rfl⟩)
  let h := b-a
  have he : a+h=b := by dsimp [h]; grind only
  have hpos : 0<h := by dsimp [h]; grind only
  have small : qabs h≤1/((D.stepPrecision p:Nat):Rat) := by
    rw [qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)]
    have w := hM K (Nat.le_max_right _ _)
    change b-a≤radius.val
    grind only [QInterval.width]
  have close := D.close a h p da (he ▸ db) daG (Rat.ne_of_gt hpos) small
  simp only [he] at close
  let k := D.evalPrecision a h p
  have da' : F.lower≤a ∧ a≤F.upper := da
  have db' : F.lower≤b ∧ b≤F.upper := db
  have daG' : G.lower≤a ∧ a≤G.upper := daG
  have converted : ((secant F.rationalValue a b).compute k).NearAt
      ((G.rationalValue a).compute k) (precisionAtStage p) := by
    simpa only [secant,FunctionOnInterval.rationalValue,dif_pos da',dif_pos db',dif_pos daG',
      RealRaw.scaleRat,RealRaw.scaleRatCompute,HSub.hSub,RealRaw.sub,RealRaw.subCompute,
      QInterval.differenceQuotient,QInterval.divRat,QInterval.scaleRat,QInterval.sub,
      intervalNearAtPrecision,k,h] using close
  rcases converted with ⟨h1,h2,h3,h4⟩
  have h1' : ((secant F.rationalValue a b).compute k).lo≤((G.rationalValue a).compute k).hi+tau.val := by grind only
  have h2' : ((G.rationalValue a).compute k).lo≤((secant F.rationalValue a b).compute k).hi+tau.val := by grind only
  have h3' := Rat.le_trans h3 htol
  have h4' := Rat.le_trans h4 htol
  have hs := secant_valid (F.rationalValue_valid a) (F.rationalValue_valid b)
  constructor
  · intro i j
    have bound := gd.1 0 k
    have cross := RealRaw.le_refl _ hs k j
    change (d.compute m).lo-eps.val≤((secant F.rationalValue a b).compute j).hi
    change (d.compute m).lo-tau.val≤((G.rationalValue a).compute k).hi at bound
    dsimp [tau] at bound h1' h2' h3' h4'
    grind only [QInterval.width,Rat.div_def]
  · intro i j
    have bound := gd.2 k 0
    have cross := RealRaw.le_refl _ hs i k
    change ((secant F.rationalValue a b).compute i).lo≤(d.compute m).hi+eps.val
    change ((G.rationalValue a).compute k).lo≤(d.compute m).hi+tau.val at bound
    dsimp [tau] at bound h1' h2' h3' h4'
    grind only [QInterval.width,Rat.div_def]

end ComputableAnalysis
