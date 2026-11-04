-- This module serves as the root of the `Ludwig` library.
-- Import modules here that should be built as part of the library.
import Ludwig.Basic
import Mathlib.Tactic

namespace TPwL_groups



-- Let `G` be a (multiplicative) group and let `g, h` be elements of `G`
variable {G : Type} [Group G] {g h : G}

-- good, we can multiply elements of a group
#check g * h

-- we can take inverses of elements of a group
#check g⁻¹
