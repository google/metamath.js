include "wnf.mm";
include "wal.mm";
include "wi.mm";
include "nf5r.mm";
include "syl.mm";

theorem nf5rd(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume nf5rd.1: $|- ( ph -> F/ x ps )$;





  do {
    wph;
    wps;
    vx;
    wnf;
    wps;
    wps;
    vx;
    wal;
    wi;
    nf5rd.1;
    wps;
    vx;
    nf5r;
    syl;
  };

  return $|-$ $( ph -> ( ps -> A. x ps ) )$;
}
