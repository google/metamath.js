include "weq.mm";
include "wi.mm";
include "ax6ev.mm";
include "eximii.mm";
include "19.36i.mm";

theorem spimv1(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x, vy: $setvar$ y) {
  assume spimv1.nf: $|- F/ x ps$;
  assume spimv1.1: $|- ( x = y -> ( ph -> ps ) )$;

  disjoint x y;



  do {
    wph;
    wps;
    vx;
    spimv1.nf;
    vx;
    vy;
    weq;
    wph;
    wps;
    wi;
    vx;
    vx;
    vy;
    ax6ev;
    spimv1.1;
    eximii;
    19.36i;
  };

  return $|-$ $( A. x ph -> ps )$;
}
