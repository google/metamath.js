include "wi2.mm";
include "wa.mm";
include "wi1.mm";
include "wn.mm";
include "wo.mm";
include "ax-r1.mm";
include "lear.mm";
include "bltr.mm";
include "leor.mm";
include "letr.mm";
include "womle2a.mm";

theorem womle(wva: $term$ a, wvb: $term$ b) {
  assume womle.1: $|- ( a ^ ( a ->1 b ) ) = ( a ^ ( a ->2 b ) )$;





  do {
    wva;
    wvb;
    wva;
    wva;
    wvb;
    wi2;
    #;
    wa;
    #;
    wva;
    wvb;
    wi1;
    #;
    @0;
    wn;
    #;
    @2;
    wo;
    @1;
    wva;
    @2;
    wa;
    #;
    @2;
    @4;
    @1;
    womle.1;
    ax-r1;
    wva;
    @2;
    lear;
    bltr;
    @2;
    @3;
    leor;
    letr;
    womle2a;
  };

  return $|-$ $( ( a ->2 b ) ' v ( a ->1 b ) ) = 1$;
}
