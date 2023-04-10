include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "u3lemanb.mm";
include "anor1.mm";
include "anor3.mm";
include "3tr2.mm";
include "con1.mm";

theorem u3lemnob(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    wn;
    wvb;
    wo;
    #;
    wva;
    wvb;
    wo;
    #;
    @0;
    wvb;
    wn;
    #;
    wa;
    wva;
    wn;
    @3;
    wa;
    @1;
    wn;
    @2;
    wn;
    wva;
    wvb;
    u3lemanb;
    @0;
    wvb;
    anor1;
    wva;
    wvb;
    anor3;
    3tr2;
    con1;
  };

  return $|-$ $( ( a ->3 b ) ' v b ) = ( a v b )$;
}
