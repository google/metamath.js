include "wn.mm";
include "wa.mm";
include "wo.mm";
include "anor1.mm";
include "con2.mm";
include "ran.mm";
include "ancom.mm";
include "ax-r2.mm";
include "lor.mm";
include "lea.mm";
include "oml2.mm";
include "ax-a2.mm";
include "3tr2.mm";
include "df-c1.mm";

theorem com3i(wva: $term$ a, wvb: $term$ b) {
  assume com3i.1: $|- ( a ^ ( a ' v b ) ) = ( a ^ b )$;





  do {
    wva;
    wvb;
    wva;
    wvb;
    wn;
    #;
    wa;
    #;
    @1;
    wn;
    #;
    wva;
    wa;
    #;
    wo;
    @1;
    wva;
    wvb;
    wa;
    #;
    wo;
    wva;
    @4;
    @1;
    wo;
    @3;
    @4;
    @1;
    @3;
    wva;
    wva;
    wn;
    wvb;
    wo;
    #;
    wa;
    #;
    @4;
    @3;
    @5;
    wva;
    wa;
    @6;
    @2;
    @5;
    wva;
    @1;
    @5;
    wva;
    wvb;
    anor1;
    con2;
    ran;
    @5;
    wva;
    ancom;
    ax-r2;
    com3i.1;
    ax-r2;
    lor;
    @1;
    wva;
    wva;
    @0;
    lea;
    oml2;
    @1;
    @4;
    ax-a2;
    3tr2;
    df-c1;
  };

  return $|- a C b$;
}
