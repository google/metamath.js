include "wnf.mm";
include "wn.mm";
include "nfnbi.mm";
include "biimpi.mm";

theorem nfnt(wph: $wff$ ph, vx: $setvar$ x) {





  do {
    wph;
    vx;
    wnf;
    wph;
    wn;
    vx;
    wnf;
    wph;
    vx;
    nfnbi;
    biimpi;
  };

  return $|-$ $( F/ x ph -> F/ x -. ph )$;
}
