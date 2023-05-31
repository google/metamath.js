include "wn.mm";
include "wex.mm";
include "alnex.mm";
include "mpgbi.mm";

theorem nex(wph: $wff$ ph, vx: $setvar$ x) {
  assume nex.1: $|- -. ph$;





  do {
    wph;
    wn;
    wph;
    vx;
    wex;
    wn;
    vx;
    wph;
    vx;
    alnex;
    nex.1;
    mpgbi;
  };

  return $|-$ $-. E. x ph$;
}
