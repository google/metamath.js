include "w0.mm"
include "w1.mm"

theorem t1

  assert wff - - -

  step 0) w0(): wff -
  step 1) w1(0): wff - -
  step 2) w1(1): wff - - -
end
