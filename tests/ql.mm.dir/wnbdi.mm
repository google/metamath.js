include "tb.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "dfnb.mm";
include "bi1.mm";
include "wcomorr.mm";
include "wcomcom.mm";
include "wcomcom2.mm";
include "ax-a2.mm";
include "wcbtr.mm";
include "wfh1.mm";
include "wr2.mm";

theorem wnbdi(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    tb;
    wn;
    #;
    wva;
    wvb;
    wo;
    #;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wo;
    wa;
    #;
    @1;
    @2;
    wa;
    @1;
    @3;
    wa;
    wo;
    @0;
    @4;
    wva;
    wvb;
    dfnb;
    bi1;
    @1;
    @2;
    @3;
    @1;
    wva;
    wva;
    @1;
    wva;
    wvb;
    wcomorr;
    wcomcom;
    wcomcom2;
    @1;
    wvb;
    wvb;
    @1;
    wvb;
    wvb;
    wva;
    wo;
    #;
    @1;
    wvb;
    wva;
    wcomorr;
    @5;
    @1;
    wvb;
    wva;
    ax-a2;
    bi1;
    wcbtr;
    wcomcom;
    wcomcom2;
    wfh1;
    wr2;
  };

  return $|- ( ( a == b ) ' == ( ( ( a v b ) ^ a ' ) v ( ( a v b ) ^ b ' ) ) ) = 1$;
}
