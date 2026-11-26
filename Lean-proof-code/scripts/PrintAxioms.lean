module

import GGOS.Frozen.GaussianDomination
import GGOS.Frozen.GaussianMoments
import GGOS.Frozen.PairNorm
import GGOS.Frozen.TorusEstimate
import GGOS.Frozen.TorusSymmetry
import GGOS.Frozen.PassageToLimit
import GGOS.Frozen.LimitFunctional

-- Run with `lake env lean scripts/PrintAxioms.lean` after `lake build`.
-- Expected for each: [propext, Classical.choice, Quot.sound]
#print axioms GGOS.gaussian_domination
#print axioms GGOS.gaussian_moments
#print axioms GGOS.pairNorm_finite_seminorm_admissible
#print axioms GGOS.torus_estimate
#print axioms GGOS.torus_symmetry
#print axioms GGOS.passage_to_limit
#print axioms GGOS.limit_functional
