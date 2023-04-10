include "wdcom.mm";
include "wfh1.mm";

theorem wddi1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





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
    wfh1;
  };

  return $|- ( ( a ^ ( b v c ) ) == ( ( a ^ b ) v ( a ^ c ) ) ) = 1$;
}
