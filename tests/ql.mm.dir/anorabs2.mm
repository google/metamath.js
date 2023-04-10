include "wo.mm";
include "wa.mm";
include "lea.mm";
include "lear.mm";
include "leo.mm";
include "lel2or.mm";
include "letr.mm";
include "ler2an.mm";
include "leor.mm";
include "lebi.mm";

theorem anorabs2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wva;
    wvb;
    wvc;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @1;
    @3;
    wva;
    @0;
    wva;
    @2;
    lea;
    @3;
    @2;
    @0;
    wva;
    @2;
    lear;
    wvb;
    @0;
    @1;
    wvb;
    wvc;
    leo;
    wva;
    @0;
    lear;
    lel2or;
    letr;
    ler2an;
    @1;
    wva;
    @2;
    wva;
    @0;
    lea;
    @1;
    wvb;
    leor;
    ler2an;
    lebi;
  };

  return $|- ( a ^ ( b v ( a ^ ( b v c ) ) ) ) = ( a ^ ( b v c ) )$;
}
