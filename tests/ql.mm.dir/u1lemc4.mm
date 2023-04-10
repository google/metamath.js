include "wi1.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-i1.mm";
include "comid.mm";
include "comcom2.mm";
include "fh4.mm";
include "ancom.mm";
include "wt.mm";
include "ax-a2.mm";
include "df-t.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "lan.mm";
include "an1.mm";

theorem u1lemc4(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wvb;
    wi1;
    wva;
    wn;
    #;
    wva;
    wvb;
    wa;
    wo;
    #;
    @0;
    wvb;
    wo;
    #;
    wva;
    wvb;
    df-i1;
    @1;
    @0;
    wva;
    wo;
    #;
    @2;
    wa;
    #;
    @2;
    wva;
    @0;
    wvb;
    wva;
    wva;
    wva;
    comid;
    comcom2;
    ulemc3.1;
    fh4;
    @4;
    @2;
    @3;
    wa;
    #;
    @2;
    @3;
    @2;
    ancom;
    @5;
    @2;
    wt;
    wa;
    @2;
    @3;
    wt;
    @2;
    @3;
    wva;
    @0;
    wo;
    #;
    wt;
    @0;
    wva;
    ax-a2;
    wt;
    @6;
    wva;
    df-t;
    ax-r1;
    ax-r2;
    lan;
    @2;
    an1;
    ax-r2;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( a ->1 b ) = ( a ' v b )$;
}
