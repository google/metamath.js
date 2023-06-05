include "w0.mm";
include "w1.mm";
include "t3.mm";
include "ax1.mm";

theorem t5() {





  do {
    w0;
    w1;
    w0;
    w0;
    w1;
    t3;
    ax1;
  };

  return |- "- - t - - q - - - -";
}
