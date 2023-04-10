include "wa.mm";
include "an32.mm";
include "bi1.mm";
include "wdf2le2.mm";
include "wran.mm";
include "wr2.mm";
include "wdf2le1.mm";

theorem wlel(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wle.1: $|- ( a =<2 b ) = 1$;





  do {
    wva;
    wvc;
    wa;
    #;
    wvb;
    @0;
    wvb;
    wa;
    #;
    wva;
    wvb;
    wa;
    #;
    wvc;
    wa;
    #;
    @0;
    @1;
    @3;
    wva;
    wvc;
    wvb;
    an32;
    bi1;
    @2;
    wva;
    wvc;
    wva;
    wvb;
    wle.1;
    wdf2le2;
    wran;
    wr2;
    wdf2le1;
  };

  return $|- ( ( a ^ c ) =<2 b ) = 1$;
}
