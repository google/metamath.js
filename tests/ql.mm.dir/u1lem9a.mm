include "wn.mm";
include "wi1.mm";
include "wa.mm";
include "wo.mm";
include "df-i1.mm";
include "ax-r4.mm";
include "anor1.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "lea.mm";
include "bltr.mm";

theorem u1lem9a(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wi1;
    #;
    wn;
    #;
    @0;
    @0;
    wvb;
    wa;
    #;
    wn;
    #;
    wa;
    #;
    @0;
    @2;
    @0;
    wn;
    @3;
    wo;
    #;
    wn;
    #;
    @5;
    @1;
    @6;
    @0;
    wvb;
    df-i1;
    ax-r4;
    @5;
    @7;
    @0;
    @3;
    anor1;
    ax-r1;
    ax-r2;
    @0;
    @4;
    lea;
    bltr;
  };

  return $|- ( a ' ->1 b ) ' =< a '$;
}
