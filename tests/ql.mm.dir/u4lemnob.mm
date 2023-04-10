include "wi4.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "u4lemanb.mm";
include "oran2.mm";
include "ran.mm";
include "ax-r2.mm";
include "anor1.mm";
include "anor3.mm";
include "3tr2.mm";
include "con1.mm";

theorem u4lemnob(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi4;
    #;
    wn;
    wvb;
    wo;
    #;
    wva;
    wvb;
    wn;
    #;
    wa;
    #;
    wvb;
    wo;
    #;
    @0;
    @2;
    wa;
    #;
    @3;
    wn;
    #;
    @2;
    wa;
    #;
    @1;
    wn;
    @4;
    wn;
    @5;
    wva;
    wn;
    wvb;
    wo;
    #;
    @2;
    wa;
    @7;
    wva;
    wvb;
    u4lemanb;
    @8;
    @6;
    @2;
    wva;
    wvb;
    oran2;
    ran;
    ax-r2;
    @0;
    wvb;
    anor1;
    @3;
    wvb;
    anor3;
    3tr2;
    con1;
  };

  return $|- ( ( a ->4 b ) ' v b ) = ( ( a ^ b ' ) v b )$;
}
