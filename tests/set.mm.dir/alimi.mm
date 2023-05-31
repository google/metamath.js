include "wi.mm";
include "wal.mm";
include "alim.mm";
include "mpg.mm";

theorem alimi(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume alimi.1: $|- ( ph -> ps )$;





  do {
    wph;
    wps;
    wi;
    wph;
    vx;
    wal;
    wps;
    vx;
    wal;
    wi;
    vx;
    wph;
    wps;
    vx;
    alim;
    alimi.1;
    mpg;
  };

  return $|-$ $( A. x ph -> A. x ps )$;
}
