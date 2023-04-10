include "wa.mm";
include "wo.mm";
include "lear.mm";
include "leo.mm";
include "letr.mm";

theorem leao2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wvb;
    wva;
    wa;
    wva;
    wva;
    wvc;
    wo;
    wvb;
    wva;
    lear;
    wva;
    wvc;
    leo;
    letr;
  };

  return $|- ( b ^ a ) =< ( a v c )$;
}
