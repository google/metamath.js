include "wt.mm";
include "wa.mm";
include "ancom.mm";
include "an1.mm";
include "ax-r2.mm";

theorem an1r(wva: $term$ a) {





  do {
    wt;
    wva;
    wa;
    wva;
    wt;
    wa;
    wva;
    wt;
    wva;
    ancom;
    wva;
    an1;
    ax-r2;
  };

  return $|- ( 1 ^ a ) = a$;
}
