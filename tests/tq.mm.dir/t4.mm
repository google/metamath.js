include "lexicon.mm"

include "w0.mm"
include "ax0.mm"
include "ax1.mm"

theorem t4
  assert |- - t - - q - -

  step 0) w0(): wff -
  step 1) w0(): wff -
  step 2) w0(): wff -
  step 3) w0(): wff -
  step 4) ax0(3): |- - t - q -
  step 5) ax1(0,1,2,4): |- - t - - q - -
end
