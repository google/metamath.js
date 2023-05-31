include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wi5.mm";
include "ran.mm";
include "ax-r4.mm";
include "2or.mm";
include "df-i5.mm";
include "3tr1.mm";

theorem ud5lem0b(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ud5lem0a.1: $|- a = b$;





  do {
    wva;
    wvc;
    wa;
    #;
    wva;
    wn;
    #;
    wvc;
    wa;
    #;
    wo;
    #;
    @1;
    wvc;
    wn;
    #;
    wa;
    #;
    wo;
    wvb;
    wvc;
    wa;
    #;
    wvb;
    wn;
    #;
    wvc;
    wa;
    #;
    wo;
    #;
    @7;
    @4;
    wa;
    #;
    wo;
    wva;
    wvc;
    wi5;
    wvb;
    wvc;
    wi5;
    @3;
    @9;
    @5;
    @10;
    @0;
    @6;
    @2;
    @8;
    wva;
    wvb;
    wvc;
    ud5lem0a.1;
    ran;
    @1;
    @7;
    wvc;
    wva;
    wvb;
    ud5lem0a.1;
    ax-r4;
    #;
    ran;
    2or;
    @1;
    @7;
    @4;
    @11;
    ran;
    2or;
    wva;
    wvc;
    df-i5;
    wvb;
    wvc;
    df-i5;
    3tr1;
  };

  return $|-$ $( a ->5 c ) = ( b ->5 c )$;
}
