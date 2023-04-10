include "wa.mm";
include "wo.mm";
include "lea.mm";
include "leo.mm";
include "letr.mm";

theorem leao1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    wva;
    wva;
    wvc;
    wo;
    wva;
    wvb;
    lea;
    wva;
    wvc;
    leo;
    letr;
  };

  return $|- ( a ^ b ) =< ( a v c )$;
}
