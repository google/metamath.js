include "wi1.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "df-i1.mm";
include "ax-r5.mm";
include "or32.mm";
include "ax-a2.mm";
include "lear.mm";
include "leor.mm";
include "letr.mm";
include "df-le2.mm";
include "ax-r2.mm";

theorem u1lemob(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    #;
    wvb;
    wo;
    wva;
    wn;
    #;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    wvb;
    wo;
    #;
    @1;
    wvb;
    wo;
    #;
    @0;
    @3;
    wvb;
    wva;
    wvb;
    df-i1;
    ax-r5;
    @4;
    @5;
    @2;
    wo;
    #;
    @5;
    @1;
    @2;
    wvb;
    or32;
    @6;
    @2;
    @5;
    wo;
    @5;
    @5;
    @2;
    ax-a2;
    @2;
    @5;
    @2;
    wvb;
    @5;
    wva;
    wvb;
    lear;
    wvb;
    @1;
    leor;
    letr;
    df-le2;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|-$ $( ( a ->1 b ) v b ) = ( a ' v b )$;
}
