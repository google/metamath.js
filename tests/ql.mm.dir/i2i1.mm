include "wn.mm";
include "wi2.mm";
include "wi1.mm";
include "ax-a1.mm";
include "ud2lem0b.mm";
include "ud2lem0a.mm";
include "i1i2.mm";
include "3tr1.mm";

theorem i2i1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wn;
    #;
    wn;
    #;
    wi2;
    wva;
    wn;
    #;
    wn;
    #;
    @1;
    wi2;
    wva;
    wvb;
    wi2;
    @0;
    @2;
    wi1;
    wva;
    @3;
    @1;
    wva;
    ax-a1;
    ud2lem0b;
    wvb;
    @1;
    wva;
    wvb;
    ax-a1;
    ud2lem0a;
    @0;
    @2;
    i1i2;
    3tr1;
  };

  return $|-$ $( a ->2 b ) = ( b ' ->1 a ' )$;
}
