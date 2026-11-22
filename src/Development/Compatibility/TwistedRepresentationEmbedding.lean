module

public import Mathlib

@[expose] public section

noncomputable section

namespace GlobalTheory.TwistedRepresentationEmbedding

open Module

def twist {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V) (χ : G →* Kˣ) :
    Representation K G V where
  toFun g := ((χ g : Kˣ) : K) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_smul]
    ring_nf

theorem twist_apply {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (χ : G →* Kˣ) (g : G) (v : V) : twist ρ χ g v = ((χ g : Kˣ) : K) • ρ g v := rfl

end GlobalTheory.TwistedRepresentationEmbedding
