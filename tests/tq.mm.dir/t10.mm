include "w0.mm"
include "w1.mm"
include "t9.mm"
include "ax4.mm"

theorem t10


  assert |- - - - - - DND - - - - - - - - - - - -

  step 0) w0(): wff -
  step 1) w1(0): wff - -
  step 2) w1(1): wff - - -
  step 3) w1(2): wff - - - -
  step 4) w1(3): wff - - - - -
  step 5) w0(): wff -
  step 6) w1(5): wff - -
  step 7) w1(6): wff - - -
  step 8) w1(7): wff - - - -
  step 9) w1(8): wff - - - - -
  step 10) w1(9): wff - - - - - -
  step 11) w1(10): wff - - - - - - -
  step 12) t9(): |- - - - - - DND - - - - - - -
  step 13) ax4(4,11,12): |- - - - - - DND - - - - - - - - - - - -
end
