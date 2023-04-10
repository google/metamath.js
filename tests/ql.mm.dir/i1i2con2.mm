include "wn.mm";
include "wi1.mm";
include "wi2.mm";
include "i1i2.mm";
include "ax-a1.mm";
include "ax-r1.mm";
include "ud2lem0a.mm";
include "ax-r2.mm";

theorem i1i2con2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wi1;
    wvb;
    wn;
    #;
    @0;
    wn;
    #;
    wi2;
    @1;
    wva;
    wi2;
    @0;
    wvb;
    i1i2;
    @2;
    wva;
    @1;
    wva;
    @2;
    wva;
    ax-a1;
    ax-r1;
    ud2lem0a;
    ax-r2;
  };

  return $|- ( a ' ->1 b ) = ( b ' ->2 a )$;
}
