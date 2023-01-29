lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "t9.mm";
include "ax4.mm";

theorem t10() : |- '- - - - - DND - - - - - - - - - - - -' {
  0. w0(): wff '-'
  1. w1(0): wff '- -'
  2. w1(1): wff '- - -'
  3. w1(2): wff '- - - -'
  4. w1(3): wff '- - - - -'
  5. w0(): wff '-'
  6. w1(5): wff '- -'
  7. w1(6): wff '- - -'
  8. w1(7): wff '- - - -'
  9. w1(8): wff '- - - - -'
  10. w1(9): wff '- - - - - -'
  11. w1(10): wff '- - - - - - -'
  12. t9(): |- '- - - - - DND - - - - - - -'
  13. ax4(4,11,12): |- '- - - - - DND - - - - - - - - - - - -'
}
