include "wt.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "df-t.mm";
include "ancom.mm";
include "an1.mm";
include "ax-r2.mm";
include "2or.mm";
include "ax-r1.mm";
include "df-c1.mm";

theorem comm1(wva: $term$ a) {





  do {
    wt;
    wva;
    wt;
    wva;
    wva;
    wn;
    #;
    wo;
    #;
    wt;
    wva;
    wa;
    #;
    wt;
    @0;
    wa;
    #;
    wo;
    #;
    wva;
    df-t;
    @4;
    @1;
    @2;
    wva;
    @3;
    @0;
    @2;
    wva;
    wt;
    wa;
    wva;
    wt;
    wva;
    ancom;
    wva;
    an1;
    ax-r2;
    @3;
    @0;
    wt;
    wa;
    @0;
    wt;
    @0;
    ancom;
    @0;
    an1;
    ax-r2;
    2or;
    ax-r1;
    ax-r2;
    df-c1;
  };

  return $|- 1 C a$;
}
