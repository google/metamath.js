include "wf.mm";
include "wo.mm";
include "wa.mm";
include "wn.mm";
include "ax-a2.mm";
include "or0.mm";
include "ax-r2.mm";
include "ax-r1.mm";
include "an0.mm";
include "wt.mm";
include "df-f.mm";
include "con2.mm";
include "lan.mm";
include "an1.mm";
include "2or.mm";
include "df-c1.mm";

theorem comm0(wva: $term$ a) {





  do {
    wva;
    wf;
    wva;
    wf;
    wva;
    wo;
    #;
    wva;
    wf;
    wa;
    #;
    wva;
    wf;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    @0;
    wva;
    @0;
    wva;
    wf;
    wo;
    wva;
    wf;
    wva;
    ax-a2;
    wva;
    or0;
    ax-r2;
    ax-r1;
    @4;
    @0;
    @1;
    wf;
    @3;
    wva;
    wva;
    an0;
    @3;
    wva;
    wt;
    wa;
    wva;
    @2;
    wt;
    wva;
    wf;
    wt;
    df-f;
    con2;
    lan;
    wva;
    an1;
    ax-r2;
    2or;
    ax-r1;
    ax-r2;
    df-c1;
  };

  return $|-$ $a C 0$;
}
