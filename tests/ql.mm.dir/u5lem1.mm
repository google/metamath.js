include "wi5.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "u5lemc1.mm";
include "comcom.mm";
include "u5lemc4.mm";
include "u5lemnoa.mm";
include "ax-r2.mm";

theorem u5lem1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi5;
    #;
    wva;
    wi5;
    @0;
    wn;
    wva;
    wo;
    wva;
    wvb;
    wo;
    wva;
    wvb;
    wn;
    wo;
    wa;
    @0;
    wva;
    wva;
    @0;
    wva;
    wvb;
    u5lemc1;
    comcom;
    u5lemc4;
    wva;
    wvb;
    u5lemnoa;
    ax-r2;
  };

  return $|- ( ( a ->5 b ) ->5 a ) = ( ( a v b ) ^ ( a v b ' ) )$;
}
