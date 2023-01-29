lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "ax0.mm";
include "ax1.mm";

theorem t5() : |- - p - - q - - - {
  0. w0(): wff '-'
  1. w0(): wff '-'
  2. w0(): wff '-'
  3. w1(2): wff '- -'
  4. w0(): wff '-'
  5. ax0(4): |- '- p - q - -'
  6. ax1(0,1,3,5): |- '- p - - q - - -'
}
