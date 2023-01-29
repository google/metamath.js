lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "t6.mm";
include "ax2.mm";

theorem t7() : |- 'C - - - - - -' {
  0. w0(): wff '-'
  1. w0(): wff '-'
  2. w1(1): wff '- -'
  3. w0(): wff '-'
  4. w1(3): wff '- -'
  5. w1(4): wff '- - -'
  6. w1(5): wff '- - - -'
  7. w1(6): wff '- - - - -'
  8. w1(7): wff '- - - - - -'
  9. t6(): |- '- - t - - - q - - - - - -'
  10. ax2(0,2,8,9): |- 'C - - - - - -'
}
