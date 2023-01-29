include "common.mm";
include "w0.mm";
include "w1.mm";
include "t5.mm";
include "ax1.mm";

theorem t6() : |- - - t - - - q - - - - - - {
  proof
    0. w0(): wff -
    1. w1(0): wff - -
    2. w0(): wff -
    3. w1(2): wff - -
    4. w0(): wff -
    5. w1(4): wff - -
    6. w1(5): wff - - -
    7. w1(6): wff - - - -
    8. t5(): |- - - t - - q - - - -
    9. ax1(1,3,7,8): |- - - t - - - q - - - - - -
}
