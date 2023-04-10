include "wi4.mm";
include "wn.mm";
include "wi3.mm";
include "ax-a1.mm";
include "ud4lem0a.mm";
include "ud4lem0b.mm";
include "ax-r2.mm";
include "i3i4.mm";
include "ax-r1.mm";

theorem i4i3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi4;
    #;
    wva;
    wn;
    #;
    wn;
    #;
    wvb;
    wn;
    #;
    wn;
    #;
    wi4;
    #;
    @3;
    @1;
    wi3;
    #;
    @0;
    wva;
    @4;
    wi4;
    @5;
    wvb;
    @4;
    wva;
    wvb;
    ax-a1;
    ud4lem0a;
    wva;
    @2;
    @4;
    wva;
    ax-a1;
    ud4lem0b;
    ax-r2;
    @6;
    @5;
    @3;
    @1;
    i3i4;
    ax-r1;
    ax-r2;
  };

  return $|- ( a ->4 b ) = ( b ' ->3 a ' )$;
}
