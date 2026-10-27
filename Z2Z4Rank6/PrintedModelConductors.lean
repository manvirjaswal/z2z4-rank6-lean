import Z2Z4Rank6.PrintedModelConductorValues

/-!
# Conductors of the three printed minimal equations

Jaswal, Lemma 4.1(b), Theorem 1.2(a), Proposition 7.2(a), Theorem 8.1(a),
DOI 10.5281/zenodo.23437117. The geometric conductor is defined using
minimal regular proper models. The hypotheses are the model existence theorem and Mulholland's
local-component theorems.
-/

namespace Z2Z4Rank6.PrintedModelConductors
noncomputable section
open Common.Elliptic.GeometricConductor Common.Elliptic.MulhollandModelTheorems
open PrintedModelConductorData PrintedModelConductorValues

theorem all_conductors (hModels : EllipticMinimalModelsTheorem)
    (h21 : Theorem21Components) (hOdd : Theorems23And24SemistableComponents) (i : Fin 3) :
    PrintedModelConductorData.conductor hModels i = printedConductor i :=
  conductor_eq h21 hOdd i (data hModels i)

theorem ec_conductor (hModels : EllipticMinimalModelsTheorem)
    (h21 : Theorem21Components) (hOdd : Theorems23And24SemistableComponents) :
    PrintedModelConductorData.conductor hModels 0 = 9240 := all_conductors hModels h21 hOdd 0

theorem jg_conductor (hModels : EllipticMinimalModelsTheorem)
    (h21 : Theorem21Components) (hOdd : Theorems23And24SemistableComponents) :
    PrintedModelConductorData.conductor hModels 1 = 683760 := all_conductors hModels h21 hOdd 1

theorem j2_conductor (hModels : EllipticMinimalModelsTheorem)
    (h21 : Theorem21Components) (hOdd : Theorems23And24SemistableComponents) :
    PrintedModelConductorData.conductor hModels 2 = 182747931661680 := all_conductors hModels h21 hOdd 2

end
end Z2Z4Rank6.PrintedModelConductors
