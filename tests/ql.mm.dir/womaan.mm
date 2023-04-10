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

theorem womaan(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wn;
    #;
    wva;
    @0;
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
    wva;
    @2;
    @3;
    wva;
    @1;
    leo;
    @0;
    @2;
    lear;
    lel2or;
    wva;
    @4;
    @1;
    wva;
    @3;
    leo;
    @1;
    @3;
    @4;
    @1;
    @0;
    @2;
    @0;
    wvb;
    lea;
    @1;
    wva;
    leor;
    ler2an;
    @3;
    wva;
    leor;
    letr;
    lel2or;
    lebi;
  };

  return $|-$ $( a v ( a ' ^ ( a v ( a ' ^ b ) ) ) ) = ( a v ( a ' ^ b ) )$;
}
