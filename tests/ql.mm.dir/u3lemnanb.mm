include "wi3.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "u3lemob.mm";
include "oran.mm";
include "oran2.mm";
include "3tr2.mm";
include "con1.mm";

theorem u3lemnanb(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    wn;
    wvb;
    wn;
    #;
    wa;
    #;
    wva;
    @1;
    wa;
    #;
    @0;
    wvb;
    wo;
    wva;
    wn;
    wvb;
    wo;
    @2;
    wn;
    @3;
    wn;
    wva;
    wvb;
    u3lemob;
    @0;
    wvb;
    oran;
    wva;
    wvb;
    oran2;
    3tr2;
    con1;
  };

  return $|-$ $( ( a ->3 b ) ' ^ b ' ) = ( a ^ b ' )$;
}
