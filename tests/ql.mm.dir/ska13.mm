include "tb.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "ledio.mm";
include "lea.mm";
include "letr.mm";
include "ancom.mm";
include "bltr.mm";
include "leror.mm";
include "dfb.mm";
include "ax-a2.mm";
include "le3tr1.mm";
include "sklem.mm";

theorem ska13(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    tb;
    #;
    wva;
    wn;
    #;
    wvb;
    wo;
    #;
    wva;
    wvb;
    wa;
    #;
    @1;
    wvb;
    wn;
    #;
    wa;
    wo;
    #;
    wvb;
    @1;
    wo;
    #;
    @0;
    @2;
    @5;
    @3;
    @1;
    wo;
    #;
    @6;
    @5;
    @7;
    @3;
    @4;
    wo;
    #;
    wa;
    @7;
    @3;
    @1;
    @4;
    ledio;
    @7;
    @8;
    lea;
    letr;
    @3;
    wvb;
    @1;
    @3;
    wvb;
    wva;
    wa;
    wvb;
    wva;
    wvb;
    ancom;
    wvb;
    wva;
    lea;
    bltr;
    leror;
    letr;
    wva;
    wvb;
    dfb;
    @1;
    wvb;
    ax-a2;
    le3tr1;
    sklem;
  };

  return $|- ( ( a == b ) ' v ( a ' v b ) ) = 1$;
}
