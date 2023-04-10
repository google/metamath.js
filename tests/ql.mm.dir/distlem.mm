include "wo.mm";
include "wa.mm";
include "lea.mm";
include "ler2an.mm";
include "leo.mm";
include "letr.mm";
include "ledi.mm";
include "lebi.mm";

theorem distlem(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume distlem.1: $|- ( a ^ ( b v c ) ) =< b$;





  do {
    wva;
    wvb;
    wvc;
    wo;
    #;
    wa;
    #;
    wva;
    wvb;
    wa;
    #;
    wva;
    wvc;
    wa;
    #;
    wo;
    #;
    @1;
    @2;
    @4;
    @1;
    wva;
    wvb;
    wva;
    @0;
    lea;
    distlem.1;
    ler2an;
    @2;
    @3;
    leo;
    letr;
    wva;
    wvb;
    wvc;
    ledi;
    lebi;
  };

  return $|- ( a ^ ( b v c ) ) = ( ( a ^ b ) v ( a ^ c ) )$;
}
