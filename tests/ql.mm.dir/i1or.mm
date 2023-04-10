include "wi1.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "df-i1.mm";
include "leo.mm";
include "lelan.mm";
include "lelor.mm";
include "bltr.mm";
include "leor.mm";
include "lel2or.mm";
include "ax-r1.mm";
include "lbtr.mm";

theorem i1or(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wvc;
    wva;
    wi1;
    #;
    wvc;
    wvb;
    wi1;
    #;
    wo;
    wvc;
    wn;
    #;
    wvc;
    wva;
    wvb;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wvc;
    @3;
    wi1;
    #;
    @0;
    @5;
    @1;
    @0;
    @2;
    wvc;
    wva;
    wa;
    #;
    wo;
    @5;
    wvc;
    wva;
    df-i1;
    @7;
    @4;
    @2;
    wva;
    @3;
    wvc;
    wva;
    wvb;
    leo;
    lelan;
    lelor;
    bltr;
    @1;
    @2;
    wvc;
    wvb;
    wa;
    #;
    wo;
    @5;
    wvc;
    wvb;
    df-i1;
    @8;
    @4;
    @2;
    wvb;
    @3;
    wvc;
    wvb;
    wva;
    leor;
    lelan;
    lelor;
    bltr;
    lel2or;
    @6;
    @5;
    wvc;
    @3;
    df-i1;
    ax-r1;
    lbtr;
  };

  return $|- ( ( c ->1 a ) v ( c ->1 b ) ) =< ( c ->1 ( a v b ) )$;
}
