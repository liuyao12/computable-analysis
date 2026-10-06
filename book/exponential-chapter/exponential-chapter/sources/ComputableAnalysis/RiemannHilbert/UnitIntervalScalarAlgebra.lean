import ComputableAnalysis.RiemannHilbert.UnitIntervalHalves
import ComputableAnalysis.RiemannHilbert.UnitSquareContinuity

/-! Scalar continuity laws for arbitrary supplied interval maps, together
with executable composition, sum, negation and product moduli when supplied.
The topological laws do not require a chosen global precision schedule. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory DomainFunctions

theorem ScalarContinuous.precompose {f : Point → Scalar} {g : Point → Point}
    (hf : ScalarContinuous f) (hg : Continuous g) : ScalarContinuous (fun t => f (g t)) :=
  fun D hD => hg _ (hf D hD)

theorem ScalarContinuous.add {f g : Point → Scalar} (hf : ScalarContinuous f) (hg : ScalarContinuous g)
    (hfc : ∀ s t, s ≈ t → f s ≈ f t) (hgc : ∀ s t, s ≈ t → g s ≈ g t) :
    ScalarContinuous (fun t => scalarSum (f t) (g t)) := by
  intro D hD
  refine ⟨fun s t hst => hD.invariant _ _ (add_equiv (hfc s t hst) (hgc s t hst)),?_⟩
  intro s hs
  obtain ⟨r,hr⟩ := hD.neighborhood (scalarSum (f s) (g s)) hs
  let eps := halfError r
  have hF := hf (ScalarTopology.ball (f s) eps) (ScalarTopology.isOpen_ball _ _)
  have hG := hg (ScalarTopology.ball (g s) eps) (ScalarTopology.isOpen_ball _ _)
  obtain ⟨u,hu⟩ := hF.neighborhood s (ScalarTopology.ball_center _ _)
  obtain ⟨v,hv⟩ := hG.neighborhood s (ScalarTopology.ball_center _ _)
  refine ⟨minRadius u v,?_⟩
  intro t ht
  have hb := LocalODE.small_add
    (ScalarTopology.ball_bound _ _ _ (hu t (ht.mono (minRadius_left _ _))))
    (ScalarTopology.ball_bound _ _ _ (hv t (ht.mono (minRadius_right _ _))))
  have he : eps.val+eps.val=r.val := by have h := halfError_identity r; dsimp [eps]; grind only
  rw [he] at hb
  exact hr (scalarSum (f t) (g t)) (Small.congr
    (add_valid (sub_valid (f t).property (f s).property) (sub_valid (g t).property (g s).property))
    (sub_valid (scalarSum (f t) (g t)).property (scalarSum (f s) (g s)).property)
    (equiv_symm (scalarSum_difference _ _ _ _)) hb)

theorem ScalarContinuous.neg {f : Point → Scalar} (hf : ScalarContinuous f) : ScalarContinuous (fun t => scalarNeg (f t)) := by
  intro D hD
  apply hf (fun z => D (scalarNeg z))
  refine ⟨fun z w hzw => hD.invariant _ _ (neg_equiv hzw),?_⟩
  intro a ha
  obtain ⟨r,hr⟩ := hD.neighborhood (scalarNeg a) ha
  refine ⟨r,fun z hz => hr (scalarNeg z) ?_⟩
  exact Small.congr (neg_valid (sub_valid z.property a.property))
    (sub_valid (scalarNeg z).property (scalarNeg a).property)
    (equiv_symm (scalarNeg_difference z a)) (SeriesLimitLaws.small_neg hz)

theorem ScalarContinuous.postcompose {f : Point → Scalar} (hf : ScalarContinuous f) (g : DomainFunctions.Map)
    (hg : DomainFunctions.OpenDomain g) (hc : ContinuousOn g.domain g.eval) (hmem : ∀ t, g.domain (f t)) :
    ScalarContinuous (fun t => g.eval (f t) (hmem t)) := by
  intro D hD
  have h := hf (ScalarTopology.preimage g D) (ScalarTopology.isOpen_preimage g hg hc D hD)
  exact UnitInterval.isOpen_congr (fun t => ⟨fun ⟨_,ht⟩ => ht,fun ht => ⟨hmem t,ht⟩⟩) h

def ScalarContinuousData.precompose {f : Point → Scalar} (hf : ScalarContinuousData f)
    (g : Point → Point) (hg : ContinuousData g) : ScalarContinuousData (fun t => f (g t)) where
  congr s t hst := hf.congr _ _ (hg.congr s t hst)
  delta s eps := hg.delta s (hf.delta (g s) eps)
  estimate s eps t ht := hf.estimate (g s) eps (g t) (hg.estimate s _ t ht)

def ScalarContinuousData.postcompose {f : Point → Scalar} (hf : ScalarContinuousData f)
    (g : DomainFunctions.Map) (hg : ContinuousOn g.domain g.eval) (hmem : ∀ t, g.domain (f t)) :
    ScalarContinuousData (fun t => g.eval (f t) (hmem t)) where
  congr s t hst := g.eval_congr _ _ (hmem s) (hmem t) (hf.congr s t hst)
  delta s eps := hf.delta s (hg.delta (f s) (hmem s) eps)
  estimate s eps t ht := hg.estimate _ (hmem s) eps _ (hmem t) (hf.estimate s _ t ht)

def ScalarContinuousData.add {f g : Point → Scalar} (hf : ScalarContinuousData f) (hg : ScalarContinuousData g) :
    ScalarContinuousData (fun t => scalarSum (f t) (g t)) :=
  ((UnitSquare.first hf).add (UnitSquare.first hg)).diagonal

def ScalarContinuousData.neg {f : Point → Scalar} (hf : ScalarContinuousData f) :
    ScalarContinuousData (fun t => scalarNeg (f t)) := (UnitSquare.first hf).neg.diagonal

def ScalarContinuousData.product {f g : Point → Scalar} (hf : ScalarContinuousData f) (hg : ScalarContinuousData g) :
    ScalarContinuousData (fun t => scalarProduct (f t) (g t)) :=
  ((UnitSquare.first hf).product (UnitSquare.first hg)).diagonal

end ComputableAnalysis.RiemannHilbert.UnitInterval
