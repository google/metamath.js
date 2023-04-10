include "wi4.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "u4lemob.mm";
include "oran.mm";
include "oran2.mm";
include "3tr2.mm";
include "con1.mm";

theorem u4lemnanb(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi4;
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
    u4lemob;
    @0;
    wvb;
    oran;
    wva;
    wvb;
    oran2;
    3tr2;
    con1;
  };

  return $|- ( ( a ->4 b ) ' ^ b ' ) = ( a ^ b ' )$;
}
