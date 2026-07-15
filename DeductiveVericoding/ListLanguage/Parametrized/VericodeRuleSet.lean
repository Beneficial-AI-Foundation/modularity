import Aesop

/- Rule set backing the `vericode` tactic for the parametrized list language.

Aesop rule sets are only visible to files that *import* the file declaring them, so this
declaration lives in its own module: `Tactics.lean` imports it, registers the vericoding
combinators into it, and defines `vericode` as a search over it. The name is kept distinct
from the `Vericode` rule set used by the category-theory modules so the two never collide. -/
declare_aesop_rule_sets [VericodeP]
