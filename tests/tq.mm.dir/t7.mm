include "lexicon.mm"

include "w0.mm"
include "w1.mm"
include "t6.mm"
include "ax2.mm"

theorem t7
  assert |- C - - - - - -

  step 0) w0(): wff -
  step 1) w0(): wff -
  step 2) w1(1): wff - -
  step 3) w0(): wff -
  step 4) w1(3): wff - -
  step 5) w1(4): wff - - -
  step 6) w1(5): wff - - - -
  step 7) w1(6): wff - - - - -
  step 8) w1(7): wff - - - - - -
  step 9) t6(): |- - - t - - - q - - - - - -
  step 10) ax2(0,2,8,9): |- C - - - - - -
end
