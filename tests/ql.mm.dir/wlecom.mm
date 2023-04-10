include "wn.mm";
include "wa.mm";
include "wo.mm";
include "orabs.mm";
include "bi1.mm";
include "wr1.mm";
include "wdf2le2.mm";
include "wr5-2v.mm";
include "wr2.mm";
include "wdf-c1.mm";

theorem wlecom(wva: $term$ a, wvb: $term$ b) {
  assume wlecom.1: $|- ( a =<2 b ) = 1$;





  do {
    wva;
    wvb;
    wva;
    wva;
    wva;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wva;
    wvb;
    wa;
    #;
    @1;
    wo;
    @2;
    wva;
    @2;
    wva;
    wva;
    @0;
    orabs;
    bi1;
    wr1;
    wva;
    @3;
    @1;
    @3;
    wva;
    wva;
    wvb;
    wlecom.1;
    wdf2le2;
    wr1;
    wr5-2v;
    wr2;
    wdf-c1;
  };

  return $|-$ $C ( a , b ) = 1$;
}
