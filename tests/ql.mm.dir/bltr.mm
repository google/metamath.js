include "wo.mm";
include "ax-r5.mm";
include "df-le2.mm";
include "ax-r2.mm";
include "df-le1.mm";

theorem bltr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume bltr.1: $|- a = b$;
  assume bltr.2: $|- b =< c$;





  do {
    wva;
    wvc;
    wva;
    wvc;
    wo;
    wvb;
    wvc;
    wo;
    wvc;
    wva;
    wvb;
    wvc;
    bltr.1;
    ax-r5;
    wvb;
    wvc;
    bltr.2;
    df-le2;
    ax-r2;
    df-le1;
  };

  return $|-$ $a =< c$;
}
