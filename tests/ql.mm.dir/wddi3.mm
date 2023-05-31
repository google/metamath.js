include "wdcom.mm";
include "wfh3.mm";

theorem wddi3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wva;
    wvb;
    wdcom;
    wva;
    wvc;
    wdcom;
    wfh3;
  };

  return $|-$ $( ( a v ( b ^ c ) ) == ( ( a v b ) ^ ( a v c ) ) ) = 1$;
}
