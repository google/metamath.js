include "wa.mm";
include "wo.mm";
include "lear.mm";
include "leor.mm";
include "letr.mm";

theorem leao4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wvb;
    wva;
    wa;
    wva;
    wvc;
    wva;
    wo;
    wvb;
    wva;
    lear;
    wva;
    wvc;
    leor;
    letr;
  };

  return $|- ( b ^ a ) =< ( c v a )$;
}
