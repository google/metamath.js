include "w0.mm";
include "w1.mm";
include "t5.mm";
include "ax1.mm";

theorem t6() {





  do {
    w0;
    w1;
    w0;
    w1;
    w0;
    w1;
    w1;
    w1;
    t5;
    ax1;
  };

  return $|- - - t - - - q - - - - - -$;
}
