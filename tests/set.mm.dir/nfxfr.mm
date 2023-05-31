include "wnf.mm";
include "nfbii.mm";
include "mpbir.mm";

theorem nfxfr(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume nfbii.1: $|- ( ph <-> ps )$;
  assume nfxfr.2: $|- F/ x ps$;





  do {
    wph;
    vx;
    wnf;
    wps;
    vx;
    wnf;
    nfxfr.2;
    wph;
    wps;
    vx;
    nfbii.1;
    nfbii;
    mpbir;
  };

  return $|-$ $F/ x ph$;
}
