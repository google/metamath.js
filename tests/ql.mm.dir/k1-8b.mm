include "wo.mm";
include "wn.mm";
include "wa.mm";
include "ax-a1.mm";
include "lan.mm";
include "ror.mm";
include "orcom.mm";
include "3tr.mm";
include "lbtr.mm";
include "k1-8a.mm";
include "ran.mm";
include "tr.mm";

theorem k1-8b(wvc: $term$ c, wvx: $term$ x, wvy: $term$ y) {
  assume k1-8b.1: $|- y ' = ( ( y ' ^ c ) v ( y ' ^ c ' ) )$;
  assume k1-8b.2: $|- x =< c$;
  assume k1-8b.3: $|- y =< c '$;





  do {
    wvy;
    wvy;
    wvx;
    wo;
    #;
    wvc;
    wn;
    #;
    wa;
    wvx;
    wvy;
    wo;
    #;
    @1;
    wa;
    @1;
    wvy;
    wvx;
    wvy;
    wn;
    #;
    @3;
    wvc;
    wa;
    #;
    @3;
    @1;
    wa;
    #;
    wo;
    @3;
    @1;
    wn;
    #;
    wa;
    #;
    @5;
    wo;
    @5;
    @7;
    wo;
    k1-8b.1;
    @4;
    @7;
    @5;
    wvc;
    @6;
    @3;
    wvc;
    ax-a1;
    #;
    lan;
    ror;
    @7;
    @5;
    orcom;
    3tr;
    k1-8b.3;
    wvx;
    wvc;
    @6;
    k1-8b.2;
    @8;
    lbtr;
    k1-8a;
    @0;
    @2;
    @1;
    wvy;
    wvx;
    orcom;
    ran;
    tr;
  };

  return $|- y = ( ( x v y ) ^ c ' )$;
}
