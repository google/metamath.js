include "wnf.mm";
include "wn.mm";
include "nfnt.mm";
include "syl.mm";

theorem nfnd(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {
  assume nfnd.1: $|- ( ph -> F/ x ps )$;





  do {
    wph;
    wps;
    vx;
    wnf;
    wps;
    wn;
    vx;
    wnf;
    nfnd.1;
    wps;
    vx;
    nfnt;
    syl;
  };

  return $|-$ $( ph -> F/ x -. ps )$;
}
