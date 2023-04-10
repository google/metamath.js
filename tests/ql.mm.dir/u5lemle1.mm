include "wi5.mm";
include "wn.mm";
include "wo.mm";
include "wt.mm";
include "lecom.mm";
include "u5lemc4.mm";
include "sklem.mm";
include "ax-r2.mm";

theorem u5lemle1(wva: $term$ a, wvb: $term$ b) {
  assume ulemle1.1: $|- a =< b$;





  do {
    wva;
    wvb;
    wi5;
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
    u5lemc4;
    wva;
    wvb;
    ulemle1.1;
    sklem;
    ax-r2;
  };

  return $|- ( a ->5 b ) = 1$;
}
