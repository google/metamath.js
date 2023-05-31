include "wi3.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "anor2.mm";
include "anor1.mm";
include "u3lemona.mm";
include "ax-r4.mm";
include "ax-r1.mm";
include "ax-r2.mm";

theorem u3lemnaa(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    wn;
    wva;
    wa;
    @0;
    wva;
    wn;
    #;
    wo;
    #;
    wn;
    #;
    wva;
    wvb;
    wn;
    wa;
    #;
    @0;
    wva;
    anor2;
    @4;
    @3;
    @4;
    @1;
    wvb;
    wo;
    #;
    wn;
    #;
    @3;
    wva;
    wvb;
    anor1;
    @3;
    @6;
    @2;
    @5;
    wva;
    wvb;
    u3lemona;
    ax-r4;
    ax-r1;
    ax-r2;
    ax-r1;
    ax-r2;
  };

  return $|-$ $( ( a ->3 b ) ' ^ a ) = ( a ^ b ' )$;
}
