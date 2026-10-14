import ComputableAnalysis.Basic

/-! Classical totality of represented order, proved from interval overlap. -/
namespace ComputableAnalysis.ModularForms

theorem representedReal_le_total (x y : RealRaw) (hx : x.Valid) (hy : y.Valid) :
    RealRaw.Le x y ∨ RealRaw.Le y x := by
  classical
  by_cases h : RealRaw.Le x y
  · exact Or.inl h
  · right
    have hg : ∃ n m, ¬(x.compute n).lo≤(y.compute m).hi := by
      apply Classical.byContradiction
      intro hn
      apply h
      intro n m
      apply Classical.byContradiction
      intro hh
      exact hn ⟨n,m,hh⟩
    obtain ⟨a,b,hab⟩ := hg
    intro n m
    have hxam := (RealRaw.compareAt_overlap_iff x x a m).mp
      (RealRaw.allStagesOverlap_refl x hx a m)
    have hynb := (RealRaw.compareAt_overlap_iff y y n b).mp
      (RealRaw.allStagesOverlap_refl y hy n b)
    have hxa := hxam.1
    have hyb := hynb.1
    grind only

end ComputableAnalysis.ModularForms
