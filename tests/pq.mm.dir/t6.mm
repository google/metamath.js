include "w0.mm"
include "w1.mm"
include "t5.mm"
include "ax1.mm"

theorem t6



  assert |- - p - - - q - - - -

  step 0) w0(): wff -
  step 1) w0(): wff -
  step 2) w1(1): wff - -
  step 3) w0(): wff -
  step 4) w1(3): wff - -
  step 5) w1(4): wff - - -
  step 6) t5(): |- - p - - q - - -
  step 7) ax1(0,2,5,6): |- - p - - - q - - - -
end
