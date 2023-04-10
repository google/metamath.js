include "wa.mm";
include "leran.mm";
include "lelan.mm";
include "letr.mm";

theorem le2an(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume le2.1: $|- a =< b$;
  assume le2.2: $|- c =< d$;





  do {
    wva;
    wvc;
    wa;
    wvb;
    wvc;
    wa;
    wvb;
    wvd;
    wa;
    wva;
    wvb;
    wvc;
    le2.1;
    leran;
    wvc;
    wvd;
    wvb;
    le2.2;
    lelan;
    letr;
  };

  return $|- ( a ^ c ) =< ( b ^ d )$;
}
