include "w0.mm"
include "w1.mm"
include "ax3.mm"
include "ax4.mm"
include "ax5.mm"
include "ax7.mm"

theorem t11


  assert |- P - - -

  step 0) w0(): wff -
  step 1) w1(0): wff - -
  step 2) w0(): wff -
  step 3) w1(2): wff - -
  step 4) w1(3): wff - - -
  step 5) w0(): wff -
  step 6) w1(5): wff - -
  step 7) w0(): wff -
  step 8) w0(): wff -
  step 9) w0(): wff -
  step 10) ax3(8,9): |- - - DND -
  step 11) ax4(6,7,10): |- - - DND - - -
  step 12) ax5(4,11): |- - - - DF - -
  step 13) ax7(1,12): |- P - - -
end
