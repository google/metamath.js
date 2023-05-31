include "wa.mm";
include "wo.mm";
include "wr1.mm";
include "wlan.mm";
include "wa5c.mm";
include "wr2.mm";

theorem wleoa(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wleoa.1: $|- ( ( a v c ) == b ) = 1$;





  do {
    wva;
    wvb;
    wa;
    wva;
    wva;
    wvc;
    wo;
    #;
    wa;
    wva;
    wvb;
    @0;
    wva;
    @0;
    wvb;
    wleoa.1;
    wr1;
    wlan;
    wva;
    wvc;
    wa5c;
    wr2;
  };

  return $|-$ $( ( a ^ b ) == a ) = 1$;
}
