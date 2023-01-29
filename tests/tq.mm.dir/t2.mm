include "common.mm";
include "w0.mm";
include "ax0.mm";

theorem t2() : |- - t - q - {
  proof
    0. w0(): wff -
    1. ax0(0): |- - t - q -
}
