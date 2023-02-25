include "lexicon.mm"
include "w0.mm"
include "w1.mm"
include "ax3.mm"

theorem t8

  assert |- - - - - - DND - -
  proof
    0. w0(): wff -
    1. w1(0): wff - -
    2. w0(): wff -
    3. w1(2): wff - -
    4. w1(3): wff - - -
    5. ax3(1,4): |- - - - - - DND - -
end
