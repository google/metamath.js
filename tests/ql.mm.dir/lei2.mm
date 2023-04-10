include "wo.mm";
include "tb.mm";
include "wn.mm";
include "wa.mm";
include "wle2.mm";
include "wi2.mm";
include "mi.mm";
include "df-le.mm";
include "df-i2.mm";
include "3tr1.mm";

theorem lei2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wo;
    wvb;
    tb;
    wvb;
    wva;
    wn;
    wvb;
    wn;
    wa;
    wo;
    wva;
    wvb;
    wle2;
    wva;
    wvb;
    wi2;
    wva;
    wvb;
    mi;
    wva;
    wvb;
    df-le;
    wva;
    wvb;
    df-i2;
    3tr1;
  };

  return $|-$ $( a =<2 b ) = ( a ->2 b )$;
}
