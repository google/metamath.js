include "wi2.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-i2.mm";
include "comcom3.mm";
include "comcom4.mm";
include "fh4.mm";
include "wt.mm";
include "ax-a2.mm";
include "df-t.mm";
include "ax-r1.mm";
include "2an.mm";
include "an1.mm";
include "ax-r2.mm";

theorem u2lemc4(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wvb;
    wi2;
    wvb;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wa;
    wo;
    #;
    @0;
    wvb;
    wo;
    #;
    wva;
    wvb;
    df-i2;
    @2;
    wvb;
    @0;
    wo;
    #;
    wvb;
    @1;
    wo;
    #;
    wa;
    #;
    @3;
    @0;
    wvb;
    @1;
    wva;
    wvb;
    ulemc3.1;
    comcom3;
    wva;
    wvb;
    ulemc3.1;
    comcom4;
    fh4;
    @6;
    @3;
    wt;
    wa;
    @3;
    @4;
    @3;
    @5;
    wt;
    wvb;
    @0;
    ax-a2;
    wt;
    @5;
    wvb;
    df-t;
    ax-r1;
    2an;
    @3;
    an1;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|- ( a ->2 b ) = ( a ' v b )$;
}
