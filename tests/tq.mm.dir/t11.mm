include "w0.mm";
include "w1.mm";
include "ax3.mm";
include "ax4.mm";
include "ax5.mm";
include "ax7.mm";

theorem t11() {





  do {
    w0;
    w1;
    w0;
    w1;
    w1;
    w0;
    w1;
    w0;
    w0;
    w0;
    ax3;
    ax4;
    ax5;
    ax7;
  };

  return |- "P - - -";
}
