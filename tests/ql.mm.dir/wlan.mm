include "wa.mm";
include "tb.mm";
include "wt.mm";
include "ancom.mm";
include "2bi.mm";
include "wran.mm";
include "ax-r2.mm";

theorem wlan(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wlan.1: $|- ( a == b ) = 1$;





  do {
    wvc;
    wva;
    wa;
    #;
    wvc;
    wvb;
    wa;
    #;
    tb;
    wva;
    wvc;
    wa;
    #;
    wvb;
    wvc;
    wa;
    #;
    tb;
    wt;
    @0;
    @2;
    @1;
    @3;
    wvc;
    wva;
    ancom;
    wvc;
    wvb;
    ancom;
    2bi;
    wva;
    wvb;
    wvc;
    wlan.1;
    wran;
    ax-r2;
  };

  return $|-$ $( ( c ^ a ) == ( c ^ b ) ) = 1$;
}
