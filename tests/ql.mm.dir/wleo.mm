include "wo.mm";
include "wa5c.mm";
include "wdf2le1.mm";

theorem wleo(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wo;
    wva;
    wvb;
    wa5c;
    wdf2le1;
  };

  return $|-$ $( a =<2 ( a v b ) ) = 1$;
}
