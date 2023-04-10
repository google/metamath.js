include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wi1.mm";
include "ancom.mm";
include "ax-r5.mm";
include "ax-a2.mm";
include "ax-r2.mm";
include "lear.mm";
include "leror.mm";
include "bltr.mm";
include "comcom.mm";
include "df-c2.mm";
include "df-i1.mm";
include "le3tr1.mm";

theorem comi1(wva: $term$ a, wvb: $term$ b) {
  assume comi1.1: $|- a C b$;





  do {
    wvb;
    wva;
    wa;
    #;
    wvb;
    wva;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    @1;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    wvb;
    wva;
    wvb;
    wi1;
    @3;
    @2;
    @4;
    wo;
    #;
    @5;
    @3;
    @4;
    @2;
    wo;
    @6;
    @0;
    @4;
    @2;
    wvb;
    wva;
    ancom;
    ax-r5;
    @4;
    @2;
    ax-a2;
    ax-r2;
    @2;
    @1;
    @4;
    wvb;
    @1;
    lear;
    leror;
    bltr;
    wvb;
    wva;
    wva;
    wvb;
    comi1.1;
    comcom;
    df-c2;
    wva;
    wvb;
    df-i1;
    le3tr1;
  };

  return $|-$ $b =< ( a ->1 b )$;
}
