include "w0.mm"
include "w1.mm"
include "t5.mm"
include "ax1.mm"

theorem t6


  assert |- - - t - - - q - - - - - -

  step 0) w0(): wff -
  step 1) w1(0): wff - -
  step 2) w0(): wff -
  step 3) w1(2): wff - -
  step 4) w0(): wff -
  step 5) w1(4): wff - -
  step 6) w1(5): wff - - -
  step 7) w1(6): wff - - - -
  step 8) t5(): |- - - t - - q - - - -
  step 9) ax1(1,3,7,8): |- - - t - - - q - - - - - -
end
