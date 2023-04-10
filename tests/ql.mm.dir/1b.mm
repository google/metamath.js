include "wt.mm";
include "tb.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "dfb.mm";
include "wf.mm";
include "ancom.mm";
include "df-f.mm";
include "ax-r1.mm";
include "lan.mm";
include "ax-r2.mm";
include "2or.mm";
include "an1.mm";
include "an0.mm";
include "or0.mm";

theorem 1b(wva: $term$ a) {





  do {
    wt;
    wva;
    tb;
    wt;
    wva;
    wa;
    #;
    wt;
    wn;
    #;
    wva;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wva;
    wt;
    wva;
    dfb;
    @4;
    wva;
    wf;
    wo;
    #;
    wva;
    @4;
    wva;
    wt;
    wa;
    #;
    @2;
    wf;
    wa;
    #;
    wo;
    @5;
    @0;
    @6;
    @3;
    @7;
    wt;
    wva;
    ancom;
    @3;
    @2;
    @1;
    wa;
    @7;
    @1;
    @2;
    ancom;
    @1;
    wf;
    @2;
    wf;
    @1;
    df-f;
    ax-r1;
    lan;
    ax-r2;
    2or;
    @6;
    wva;
    @7;
    wf;
    wva;
    an1;
    @2;
    an0;
    2or;
    ax-r2;
    wva;
    or0;
    ax-r2;
    ax-r2;
  };

  return $|- ( 1 == a ) = a$;
}
