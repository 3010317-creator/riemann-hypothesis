module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmonicValueIntegral

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

end Sym

namespace Sym

variable {k : Type} [CommRing k] {σ : Type}

end Sym

namespace Sym

variable {k : Type} [CommRing k]

theorem const_ev {m n d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p q, constantCoeff (a p q) = 0) (g : PS k m d) :
    constantCoeff (ev a g) = constantCoeff g := by
  unfold ev
  exact _root_.ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.const_subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) g

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {k : Type} [CommRing k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

namespace Sym

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
  [Algebra ℚ k] [Algebra R k]

end Sym

end Formalism.MainNotions.ModuliIntegralCharts.H1
