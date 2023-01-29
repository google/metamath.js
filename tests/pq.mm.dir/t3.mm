lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "ax0.mm";

theorem t3() : |- - - p - q - - - {
  0. w0(): wff '-'
  1. w1(0): wff '- -'
  2. ax0(1): |- '- - p - q - - -'
}
