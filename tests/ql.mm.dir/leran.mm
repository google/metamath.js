include "wa.mm";
include "anandir.mm";
include "ax-r1.mm";
include "df2le2.mm";
include "ran.mm";
include "ax-r2.mm";
include "df2le1.mm";

theorem leran(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume le.1: $|- a =< b$;





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
    wva;
    wvb;
    wvc;
    anandir;
    ax-r1;
    @3;
    wva;
    wvc;
    wva;
    wvb;
    le.1;
    df2le2;
    ran;
    ax-r2;
    df2le1;
  };

  return $|- ( a ^ c ) =< ( b ^ c )$;
}
