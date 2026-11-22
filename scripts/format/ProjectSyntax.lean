/-
The only syntax the project (as of pull request 66) declares for use across files. Each line
reproduces the syntax of the original declaration in its original namespace; the expansions are
irrelevant to parsing and are left out.

  GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean
  Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsClassSystem.lean
  Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/CovolOneIntegralAdd.lean
  Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExistsRow.lean
-/
namespace GroundTheory.LocalField.Abstract
scoped notation "ℤ̂" => Nat
end GroundTheory.LocalField.Abstract

namespace GlobalTheory.TwInputs.Move
scoped syntax "geo_cases " ident ident ident : tactic
scoped syntax "base_cases " ident ident ident : tactic
end GlobalTheory.TwInputs.Move

namespace GlobalTheory.MixModel
scoped infixl:70 " ⬝ " => HMul.hMul
end GlobalTheory.MixModel

syntax "kc%" term:max : term
