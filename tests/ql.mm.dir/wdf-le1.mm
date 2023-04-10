include "wle2.mm";
include "wo.mm";
include "tb.mm";
include "wt.mm";
include "df-le.mm";
include "ax-r2.mm";

theorem wdf-le1(wva: $term$ a, wvb: $term$ b) {
  assume wdf-le1.1: $|- ( ( a v b ) == b ) = 1$;





  do {
    wva;
    wvb;
    wle2;
    wva;
    wvb;
    wo;
    wvb;
    tb;
    wt;
    wva;
    wvb;
    df-le;
    wdf-le1.1;
    ax-r2;
  };

  return $|- ( a =<2 b ) = 1$;
}
