include "wi1.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-i1.mm";
include "ran.mm";
include "ancom.mm";
include "anabs.mm";
include "ax-r2.mm";

theorem u1lemana(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    #;
    wva;
    wn;
    #;
    wa;
    @1;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    @1;
    wa;
    #;
    @1;
    @0;
    @3;
    @1;
    wva;
    wvb;
    df-i1;
    ran;
    @4;
    @1;
    @3;
    wa;
    @1;
    @3;
    @1;
    ancom;
    @1;
    @2;
    anabs;
    ax-r2;
    ax-r2;
  };

  return $|- ( ( a ->1 b ) ^ a ' ) = a '$;
}
