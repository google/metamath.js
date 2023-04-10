include "wo.mm";
include "ax-r5.mm";
include "oridm.mm";
include "ax-r2.mm";
include "df-le1.mm";

theorem bile(wva: $term$ a, wvb: $term$ b) {
  assume bile.1: $|- a = b$;





  do {
    wva;
    wvb;
    wva;
    wvb;
    wo;
    wvb;
    wvb;
    wo;
    wvb;
    wva;
    wvb;
    wvb;
    bile.1;
    ax-r5;
    wvb;
    oridm;
    ax-r2;
    df-le1;
  };

  return $|-$ $a =< b$;
}
