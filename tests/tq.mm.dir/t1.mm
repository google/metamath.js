include "common.mm";
include "w0.mm";
include "w1.mm";

theorem t1() : wff - - - {
  proof
    0. w0(): wff -
    1. w1(0): wff - -
    2. w1(1): wff - - -
}
