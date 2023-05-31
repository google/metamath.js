include "wnf.mm";
include "wn.mm";
include "nfnt.mm";
include "ax-mp.mm";

theorem nfn(wph: $wff$ ph, vx: $setvar$ x) {
  assume nfn.1: $|- F/ x ph$;





  do {
    wph;
    vx;
    wnf;
    wph;
    wn;
    vx;
    wnf;
    nfn.1;
    wph;
    vx;
    nfnt;
    ax-mp;
  };

  return $|-$ $F/ x -. ph$;
}
