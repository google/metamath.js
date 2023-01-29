lexicon "lexicon.mm";
include "w0.mm";
include "w1.mm";
include "ax3.mm";
include "ax4.mm";
include "ax5.mm";
include "ax7.mm";

theorem t11() : |- 'P - - -' {
  0. w0(): wff '-'
  1. w1(0): wff '- -'
  2. w0(): wff '-'
  3. w1(2): wff '- -'
  4. w1(3): wff '- - -'
  5. w0(): wff '-'
  6. w1(5): wff '- -'
  7. w0(): wff '-'
  8. w0(): wff '-'
  9. w0(): wff '-'
  10. ax3(8,9): |- '- - DND -'
  11. ax4(6,7,10): |- '- - DND - - -'
  12. ax5(4,11): |- '- - - DF - -'
  13. ax7(1,12): |- 'P - - -'
}
