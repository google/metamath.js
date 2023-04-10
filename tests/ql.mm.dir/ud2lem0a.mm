include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wi2.mm";
include "ax-r4.mm";
include "lan.mm";
include "2or.mm";
include "df-i2.mm";
include "3tr1.mm";

theorem ud2lem0a(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ud2lem0a.1: $|- a = b$;





  do {
    wva;
    wvc;
    wn;
    #;
    wva;
    wn;
    #;
    wa;
    #;
    wo;
    wvb;
    @0;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    wvc;
    wva;
    wi2;
    wvc;
    wvb;
    wi2;
    wva;
    wvb;
    @2;
    @4;
    ud2lem0a.1;
    @1;
    @3;
    @0;
    wva;
    wvb;
    ud2lem0a.1;
    ax-r4;
    lan;
    2or;
    wvc;
    wva;
    df-i2;
    wvc;
    wvb;
    df-i2;
    3tr1;
  };

  return $|- ( c ->2 a ) = ( c ->2 b )$;
}
