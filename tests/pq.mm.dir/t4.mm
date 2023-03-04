include "w0.mm"
include "w1.mm"
include "ax0.mm"

theorem t4


  assert |- - - - p - q - - - -

  step 0) w0(): wff -
  step 1) w1(0): wff - -
  step 2) w1(1): wff - - -
  step 3) ax0(2): |- - - - p - q - - - -
end
