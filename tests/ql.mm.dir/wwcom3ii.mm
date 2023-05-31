include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wwcomd.mm";
include "lan.mm";
include "anass.mm";
include "ax-r1.mm";
include "ax-a2.mm";
include "anabs.mm";
include "ax-r2.mm";
include "2an.mm";

theorem wwcom3ii(wva: $term$ a, wvb: $term$ b) {
  assume wwcom3ii.1: $|- b ' C a$;





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wva;
    wn;
    #;
    wvb;
    wo;
    #;
    wa;
    #;
    @0;
    wva;
    wvb;
    wva;
    wo;
    #;
    wvb;
    @1;
    wo;
    #;
    wa;
    #;
    wa;
    #;
    @3;
    wvb;
    @6;
    wva;
    wvb;
    wva;
    wwcom3ii.1;
    wwcomd;
    lan;
    @7;
    wva;
    @4;
    wa;
    #;
    @5;
    wa;
    #;
    @3;
    @9;
    @7;
    wva;
    @4;
    @5;
    anass;
    ax-r1;
    @8;
    wva;
    @5;
    @2;
    @8;
    wva;
    wva;
    wvb;
    wo;
    #;
    wa;
    wva;
    @4;
    @10;
    wva;
    wvb;
    wva;
    ax-a2;
    lan;
    wva;
    wvb;
    anabs;
    ax-r2;
    wvb;
    @1;
    ax-a2;
    2an;
    ax-r2;
    ax-r2;
    ax-r1;
  };

  return $|-$ $( a ^ ( a ' v b ) ) = ( a ^ b )$;
}
