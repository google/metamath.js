
include "common.mm";
include "t0.mm";
include "ax0.mm";

theorem t3() : |- - - t - q - - {
  proof
    0. t0(): wff - -
    1. ax0(0): |- - - t - q - -
}
