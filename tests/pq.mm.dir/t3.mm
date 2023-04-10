include "w0.mm";
include "w1.mm";
include "ax0.mm";

theorem t3() {





  do {
    w0;
    w1;
    ax0;
  };

  return $|- - - p - q - - -$;
}
