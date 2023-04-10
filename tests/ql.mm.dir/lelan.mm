include "wa.mm";
include "leran.mm";
include "ancom.mm";
include "le3tr1.mm";

theorem lelan(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume lel.1: $|- a =< b$;





  do {
    wva;
    wvc;
    wa;
    wvb;
    wvc;
    wa;
    wvc;
    wva;
    wa;
    wvc;
    wvb;
    wa;
    wva;
    wvb;
    wvc;
    lel.1;
    leran;
    wvc;
    wva;
    ancom;
    wvc;
    wvb;
    ancom;
    le3tr1;
  };

  return $|- ( c ^ a ) =< ( c ^ b )$;
}
