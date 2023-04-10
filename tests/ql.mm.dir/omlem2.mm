include "wo.mm";
include "wn.mm";
include "wa.mm";
include "wt.mm";
include "ax-a2.mm";
include "anor2.mm";
include "2or.mm";
include "ax-a3.mm";
include "ax-r1.mm";
include "df-t.mm";
include "3tr1.mm";

theorem omlem2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wo;
    #;
    wn;
    #;
    wva;
    wo;
    #;
    wva;
    wn;
    @0;
    wa;
    #;
    wo;
    #;
    wva;
    @1;
    wo;
    #;
    @5;
    wn;
    #;
    wo;
    @1;
    wva;
    @3;
    wo;
    wo;
    #;
    wt;
    @2;
    @5;
    @3;
    @6;
    @1;
    wva;
    ax-a2;
    wva;
    @0;
    anor2;
    2or;
    @4;
    @7;
    @1;
    wva;
    @3;
    ax-a3;
    ax-r1;
    @5;
    df-t;
    3tr1;
  };

  return $|- ( ( a v b ) ' v ( a v ( a ' ^ ( a v b ) ) ) ) = 1$;
}
