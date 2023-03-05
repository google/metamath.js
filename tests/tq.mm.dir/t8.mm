include "w0.mm"
include "w1.mm"
include "ax3.mm"

theorem t8



  assert |- - - - - - DND - -

  step 0) w0(): wff -
  step 1) w1(0): wff - -
  step 2) w0(): wff -
  step 3) w1(2): wff - -
  step 4) w1(3): wff - - -
  step 5) ax3(1, 4): |- - - - - - DND - -
end
