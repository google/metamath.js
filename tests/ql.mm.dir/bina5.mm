include "wn.mm";
include "wo.mm";
include "wt.mm";
include "le1.mm";
include "df-t.mm";
include "lbtr.mm";
include "lei3.mm";

theorem bina5(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wva;
    wva;
    wn;
    wo;
    #;
    wvb;
    wt;
    @0;
    wvb;
    le1;
    wva;
    df-t;
    lbtr;
    lei3;
  };

  return $|-$ $( b ->3 ( a v a ' ) ) = 1$;
}
