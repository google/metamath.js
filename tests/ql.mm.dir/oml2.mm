include "wn.mm";
include "wo.mm";
include "wa.mm";
include "oml.mm";
include "df-le2.mm";
include "lan.mm";
include "lor.mm";
include "3tr2.mm";

theorem oml2(wva: $term$ a, wvb: $term$ b) {
  assume oml2.1: $|- a =< b$;





  do {
    wva;
    wva;
    wn;
    #;
    wva;
    wvb;
    wo;
    #;
    wa;
    #;
    wo;
    @1;
    wva;
    @0;
    wvb;
    wa;
    #;
    wo;
    wvb;
    wva;
    wvb;
    oml;
    @2;
    @3;
    wva;
    @1;
    wvb;
    @0;
    wva;
    wvb;
    oml2.1;
    df-le2;
    #;
    lan;
    lor;
    @4;
    3tr2;
  };

  return $|- ( a v ( a ' ^ b ) ) = b$;
}
