module

import GGOS.OS.FullStatement

-- Run with `lake env lean scripts/PrintAxiomsFull.lean` after `lake build`.
-- Expected: [propext, sorryAx, Classical.choice, Quot.sound]; sorryAx comes only from
-- GGOS.OS.os0Schwartz_of and GGOS.OS.rotation_invariance.
#print axioms GGOS.osterwalder_schrader_full
#print axioms GGOS.OS.os1_of_rotations
#print axioms GGOS.OS.pushT_translation
