include "wa.mm";
include "wo.mm";
include "lea.mm";
include "leor.mm";
include "letr.mm";

theorem leao3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    wva;
    wvc;
    wva;
    wo;
    wva;
    wvb;
    lea;
    wva;
    wvc;
    leor;
    letr;
  };

  return $|-$ $( a ^ b ) =< ( c v a )$;
}
