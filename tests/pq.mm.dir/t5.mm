include "w0.mm";
include "w1.mm";
include "ax0.mm";
include "ax1.mm";

theorem t5() {





  do {
    w0;
    w0;
    w0;
    w1;
    w0;
    ax0;
    ax1;
  };

  return |- "- p - - q - - -";
}
