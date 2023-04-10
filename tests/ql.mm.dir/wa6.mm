include "tb.mm";
include "wn.mm";
include "wo.mm";
include "df-b.mm";
include "bi1.mm";

theorem wa6(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    tb;
    wva;
    wn;
    wvb;
    wn;
    wo;
    wn;
    wva;
    wvb;
    wo;
    wn;
    wo;
    wva;
    wvb;
    df-b;
    bi1;
  };

  return $|- ( ( a == b ) == ( ( a ' v b ' ) ' v ( a v b ) ' ) ) = 1$;
}
