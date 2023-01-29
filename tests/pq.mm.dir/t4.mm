lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "ax0.mm";

theorem t4() : |- '- - - p - q - - - -' {
  0. w0(): wff '-'
  1. w1(0): wff '- -'
  2. w1(1): wff '- - -'
  3. ax0(2): |- '- - - p - q - - - -'
}
