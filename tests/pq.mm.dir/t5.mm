include "lexicon.mm"

include "w0.mm"
include "w1.mm"
include "ax0.mm"
include "ax1.mm"

theorem t5
  assert |- - p - - q - - -

  step 0) w0(): wff -
  step 1) w0(): wff -
  step 2) w0(): wff -
  step 3) w1(2): wff - -
  step 4) w0(): wff -
  step 5) ax0(4): |- - p - q - -
  step 6) ax1(0,1,3,5): |- - p - - q - - -
end
