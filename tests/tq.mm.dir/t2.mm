include "lexicon.mm"
include "w0.mm"
include "ax0.mm"

theorem t2

  assert |- - t - q -

  step 0) w0(): wff -
  step 1) ax0(0): |- - t - q -
end
