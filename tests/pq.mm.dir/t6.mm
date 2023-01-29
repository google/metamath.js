lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "t5.mm";
include "ax1.mm";

theorem t6() : |- - p - - - q - - - - {
  proof
    0. w0(): wff -
    1. w0(): wff -
    2. w1(1): wff - -
    3. w0(): wff -
    4. w1(3): wff - -
    5. w1(4): wff - - -
    6. t5(): |- - p - - q - - -
    7. ax1(0,2,5,6): |- - p - - - q - - - -
}
