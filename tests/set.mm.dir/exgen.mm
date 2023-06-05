include "weq.mm";
include "ax6ev.mm";
include "a1i.mm";
include "eximii.mm";

theorem exgen(wph: wff ph, vx: setvar x) {
  assume exgen.1: |- "ph";



  let vy: setvar y;

  do {
    vx;
    vy;
    weq;
    #;
    wph;
    vx;
    vx;
    vy;
    ax6ev;
    wph;
    @0;
    exgen.1;
    a1i;
    eximii;
  };

  return |- "E. x ph";
}
