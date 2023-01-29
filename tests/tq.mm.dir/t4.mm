
include "common.mm";
include "w0.mm";
include "ax0.mm";
include "ax1.mm";

theorem t4() : |- - t - - q - - {
  proof
    0. w0(): wff -
    1. w0(): wff -
    2. w0(): wff -
    3. w0(): wff -
    4. ax0(3): |- - t - q -
    5. ax1(0,1,2,4): |- - t - - q - -
}
