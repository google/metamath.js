include "wa.mm";
include "anandir.mm";
include "bi1.mm";
include "wr1.mm";
include "wdf2le2.mm";
include "wran.mm";
include "wr2.mm";
include "wdf2le1.mm";

theorem wleran(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wle.1: $|- ( a =<2 b ) = 1$;





  do {
    wva;
    wvc;
    wa;
    #;
    wvb;
    wvc;
    wa;
    #;
    @0;
    @1;
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
    @4;
    @2;
    @4;
    @2;
    wva;
    wvb;
    wvc;
    anandir;
    bi1;
    wr1;
    @3;
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

  return $|- ( ( a ^ c ) =<2 ( b ^ c ) ) = 1$;
}
