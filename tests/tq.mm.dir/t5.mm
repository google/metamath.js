include "w0.mm"
include "w1.mm"
include "t3.mm"
include "ax1.mm"

theorem t5


  assert |- - - t - - q - - - -

  step 0) w0(): wff -
  step 1) w1(0): wff - -
  step 2) w0(): wff -
  step 3) w0(): wff -
  step 4) w1(3): wff - -
  step 5) t3(): |- - - t - q - -
  step 6) ax1(1,2,4,5): |- - - t - - q - - - -
end
