include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "wt.mm";
include "lecom.mm";
include "u3lemc4.mm";
include "sklem.mm";
include "ax-r2.mm";

theorem u3lemle1(wva: $term$ a, wvb: $term$ b) {
  assume ulemle1.1: $|- a =< b$;





  do {
    wva;
    wvb;
    wi3;
    wva;
    wn;
    wvb;
    wo;
    wt;
    wva;
    wvb;
    wva;
    wvb;
    ulemle1.1;
    lecom;
    u3lemc4;
    wva;
    wvb;
    ulemle1.1;
    sklem;
    ax-r2;
  };

  return $|- ( a ->3 b ) = 1$;
}
