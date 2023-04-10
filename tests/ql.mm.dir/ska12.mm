include "tb.mm";
include "bicom.mm";
include "bi1.mm";

theorem ska12(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    tb;
    wvb;
    wva;
    tb;
    wva;
    wvb;
    bicom;
    bi1;
  };

  return $|-$ $( ( a == b ) == ( b == a ) ) = 1$;
}
