include "wa.mm";
include "le2an.mm";
include "anidm.mm";
include "lbtr.mm";

theorem lel2an(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume lel2.1: $|- a =< b$;
  assume lel2.2: $|- c =< b$;





  do {
    wva;
    wvc;
    wa;
    wvb;
    wvb;
    wa;
    wvb;
    wva;
    wvb;
    wvc;
    wvb;
    lel2.1;
    lel2.2;
    le2an;
    wvb;
    anidm;
    lbtr;
  };

  return $|- ( a ^ c ) =< b$;
}
