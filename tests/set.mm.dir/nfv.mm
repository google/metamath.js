include "ax5ea.mm";
include "nfi.mm";

theorem nfv(wph: $wff$ ph, vx: $setvar$ x) {

  disjoint ph x;



  do {
    wph;
    vx;
    wph;
    vx;
    ax5ea;
    nfi;
  };

  return $|-$ $F/ x ph$;
}
