include "wo.mm";
include "wa.mm";
include "anass.mm";
include "cm.mm";
include "ax-a2.mm";
include "ran.mm";
include "ml.mm";
include "orcom.mm";
include "3tr.mm";
include "tr.mm";

theorem vneulem2(wvu: $term$ u, wvw: $term$ w, wvx: $term$ x, wvy: $term$ y) {





  do {
    wvx;
    wvy;
    wo;
    #;
    wvu;
    wo;
    #;
    wvu;
    wvw;
    wo;
    #;
    wvw;
    wa;
    wa;
    #;
    @1;
    @2;
    wa;
    #;
    wvw;
    wa;
    #;
    @0;
    @2;
    wa;
    #;
    wvu;
    wo;
    #;
    wvw;
    wa;
    @5;
    @3;
    @1;
    @2;
    wvw;
    anass;
    cm;
    @4;
    @7;
    wvw;
    @4;
    wvu;
    @0;
    wo;
    #;
    @2;
    wa;
    #;
    wvu;
    @6;
    wo;
    #;
    @7;
    @1;
    @8;
    @2;
    @0;
    wvu;
    ax-a2;
    ran;
    @10;
    @9;
    wvu;
    @0;
    wvw;
    ml;
    cm;
    wvu;
    @6;
    orcom;
    3tr;
    ran;
    tr;
  };

  return $|- ( ( ( x v y ) v u ) ^ ( ( u v w ) ^ w ) ) = ( ( ( ( x v y ) ^ ( u v w ) ) v u ) ^ w )$;
}
