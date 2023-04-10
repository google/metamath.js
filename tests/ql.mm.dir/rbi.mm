include "tb.mm";
include "lbi.mm";
include "bicom.mm";
include "3tr1.mm";

theorem rbi(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume rbi.1: $|- a = b$;





  do {
    wvc;
    wva;
    tb;
    wvc;
    wvb;
    tb;
    wva;
    wvc;
    tb;
    wvb;
    wvc;
    tb;
    wva;
    wvb;
    wvc;
    rbi.1;
    lbi;
    wva;
    wvc;
    bicom;
    wvb;
    wvc;
    bicom;
    3tr1;
  };

  return $|- ( a == c ) = ( b == c )$;
}
