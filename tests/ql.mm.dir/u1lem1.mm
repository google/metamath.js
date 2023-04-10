include "wi1.mm";
include "wn.mm";
include "wo.mm";
include "u1lemc1.mm";
include "comcom.mm";
include "u1lemc4.mm";
include "u1lemnoa.mm";
include "ax-r2.mm";

theorem u1lem1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    #;
    wva;
    wi1;
    @0;
    wn;
    wva;
    wo;
    wva;
    @0;
    wva;
    wva;
    @0;
    wva;
    wvb;
    u1lemc1;
    comcom;
    u1lemc4;
    wva;
    wvb;
    u1lemnoa;
    ax-r2;
  };

  return $|- ( ( a ->1 b ) ->1 a ) = a$;
}
