lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "t3.mm";
include "ax1.mm";

theorem t5() : |- - - t - - q - - - - {
  0. w0(): wff '-'
  1. w1(0): wff '- -'
  2. w0(): wff '-'
  3. w0(): wff '-'
  4. w1(3): wff '- -'
  5. t3(): |- '- - t - q - -'
  6. ax1(1,2,4,5): |- '- - t - - q - - - -'
}
