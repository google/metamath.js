lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "t8.mm";
include "ax4.mm";

theorem t9() : |- - - - - - DND - - - - - - - {
  0. w0(): wff '-'
  1. w1(0): wff '- -'
  2. w1(1): wff '- - -'
  3. w1(2): wff '- - - -'
  4. w1(3): wff '- - - - -'
  5. w0(): wff '-'
  6. w1(5): wff '- -'
  7. t8(): |- '- - - - - DND - -'
  8. ax4(4,6,7): |- '- - - - - DND - - - - - - -'
}
