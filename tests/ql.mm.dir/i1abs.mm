include "wi1.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "ud1lem0c.mm";
include "ax-r5.mm";
include "comanr1.mm";
include "comorr.mm";
include "comcom6.mm";
include "fh4r.mm";
include "wt.mm";
include "orabs.mm";
include "df-a.mm";
include "lor.mm";
include "df-t.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "2an.mm";
include "an1.mm";
include "3tr.mm";

theorem i1abs(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    wn;
    #;
    wva;
    wvb;
    wa;
    #;
    wo;
    wva;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wo;
    #;
    wa;
    #;
    @1;
    wo;
    wva;
    @1;
    wo;
    #;
    @4;
    @1;
    wo;
    #;
    wa;
    #;
    wva;
    @0;
    @5;
    @1;
    wva;
    wvb;
    ud1lem0c;
    ax-r5;
    wva;
    @1;
    @4;
    wva;
    wvb;
    comanr1;
    wva;
    @4;
    @2;
    @3;
    comorr;
    comcom6;
    fh4r;
    @8;
    wva;
    wt;
    wa;
    wva;
    @6;
    wva;
    @7;
    wt;
    wva;
    wvb;
    orabs;
    @7;
    @4;
    @4;
    wn;
    #;
    wo;
    #;
    wt;
    @1;
    @9;
    @4;
    wva;
    wvb;
    df-a;
    lor;
    wt;
    @10;
    @4;
    df-t;
    ax-r1;
    ax-r2;
    2an;
    wva;
    an1;
    ax-r2;
    3tr;
  };

  return $|- ( ( a ->1 b ) ' v ( a ^ b ) ) = a$;
}
