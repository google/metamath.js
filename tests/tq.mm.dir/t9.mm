include "w0.mm"
include "w1.mm"
include "t8.mm"
include "ax4.mm"

theorem t9



  assert |- - - - - - DND - - - - - - -

  step 0) w0(): wff -
  step 1) w1(0): wff - -
  step 2) w1(1): wff - - -
  step 3) w1(2): wff - - - -
  step 4) w1(3): wff - - - - -
  step 5) w0(): wff -
  step 6) w1(5): wff - -
  step 7) t8(): |- - - - - - DND - -
  step 8) ax4(4,6,7): |- - - - - - DND - - - - - - -
end
