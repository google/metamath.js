include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wt.mm";
include "coman1.mm";
include "comcom.mm";
include "comorr.mm";
include "comcom3.mm";
include "com2an.mm";
include "fh1.mm";
include "anass.mm";
include "ax-r1.mm";
include "anidm.mm";
include "ran.mm";
include "ax-r2.mm";
include "anabs.mm";
include "omlan.mm";
include "2or.mm";
include "ax-a2.mm";
include "wi3.mm";
include "df2i3.mm";
include "lan.mm";
include "an1.mm";

theorem i3lem1(wva: $term$ a, wvb: $term$ b) {
  assume i3lem.1: $|- ( a ->3 b ) = 1$;





  do {
    wva;
    wn;
    #;
    wvb;
    wa;
    #;
    @0;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    @0;
    wt;
    wa;
    #;
    @0;
    @4;
    @0;
    @3;
    @0;
    wvb;
    wo;
    #;
    wva;
    @1;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @5;
    @10;
    @4;
    @10;
    @0;
    @3;
    wa;
    #;
    @0;
    @8;
    wa;
    #;
    wo;
    #;
    @4;
    @0;
    @3;
    @8;
    @3;
    @0;
    @0;
    @2;
    coman1;
    comcom;
    @0;
    @6;
    @7;
    @0;
    wvb;
    comorr;
    wva;
    @7;
    wva;
    @1;
    comorr;
    comcom3;
    com2an;
    fh1;
    @13;
    @3;
    @1;
    wo;
    @4;
    @11;
    @3;
    @12;
    @1;
    @11;
    @0;
    @0;
    wa;
    #;
    @2;
    wa;
    #;
    @3;
    @15;
    @11;
    @0;
    @0;
    @2;
    anass;
    ax-r1;
    @14;
    @0;
    @2;
    @0;
    anidm;
    ran;
    ax-r2;
    @12;
    @0;
    @6;
    wa;
    #;
    @7;
    wa;
    #;
    @1;
    @17;
    @12;
    @0;
    @6;
    @7;
    anass;
    ax-r1;
    @17;
    @0;
    @7;
    wa;
    @1;
    @16;
    @0;
    @7;
    @0;
    wvb;
    anabs;
    ran;
    wva;
    wvb;
    omlan;
    ax-r2;
    ax-r2;
    2or;
    @3;
    @1;
    ax-a2;
    ax-r2;
    ax-r2;
    ax-r1;
    @9;
    wt;
    @0;
    @9;
    wva;
    wvb;
    wi3;
    #;
    wt;
    @18;
    @9;
    wva;
    wvb;
    df2i3;
    ax-r1;
    i3lem.1;
    ax-r2;
    lan;
    ax-r2;
    @0;
    an1;
    ax-r2;
  };

  return $|- ( ( a ' ^ b ) v ( a ' ^ b ' ) ) = a '$;
}
