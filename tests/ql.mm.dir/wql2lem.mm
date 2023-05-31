include "wn.mm";
include "wo.mm";
include "wt.mm";
include "le1.mm";
include "wa.mm";
include "wi2.mm";
include "df-i2.mm";
include "ax-a2.mm";
include "3tr2.mm";
include "lea.mm";
include "leror.mm";
include "bltr.mm";
include "lebi.mm";

theorem wql2lem(wva: $term$ a, wvb: $term$ b) {
  assume wql2lem.1: $|- ( a ->2 b ) = 1$;





  do {
    wva;
    wn;
    #;
    wvb;
    wo;
    #;
    wt;
    @1;
    le1;
    wt;
    @0;
    wvb;
    wn;
    #;
    wa;
    #;
    wvb;
    wo;
    #;
    @1;
    wva;
    wvb;
    wi2;
    wvb;
    @3;
    wo;
    wt;
    @4;
    wva;
    wvb;
    df-i2;
    wql2lem.1;
    wvb;
    @3;
    ax-a2;
    3tr2;
    @3;
    @0;
    wvb;
    @0;
    @2;
    lea;
    leror;
    bltr;
    lebi;
  };

  return $|-$ $( a ' v b ) = 1$;
}
