include "wn.mm";
include "wa.mm";
include "wo.mm";
include "leo.mm";
include "lear.mm";
include "lel2or.mm";
include "lea.mm";
include "leor.mm";
include "ler2an.mm";
include "letr.mm";
include "lebi.mm";

theorem womaa(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wva;
    @0;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    @2;
    @0;
    @2;
    @3;
    @0;
    @1;
    leo;
    wva;
    @2;
    lear;
    lel2or;
    @0;
    @4;
    @1;
    @0;
    @3;
    leo;
    @1;
    @3;
    @4;
    @1;
    wva;
    @2;
    wva;
    wvb;
    lea;
    @1;
    @0;
    leor;
    ler2an;
    @3;
    @0;
    leor;
    letr;
    lel2or;
    lebi;
  };

  return $|-$ $( a ' v ( a ^ ( a ' v ( a ^ b ) ) ) ) = ( a ' v ( a ^ b ) )$;
}
