include "wo.mm";
include "wa.mm";
include "l42modlem2.mm";
include "l42modlem1.mm";
include "lbtr.mm";

theorem l42mod(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d, wve: $term$ e) {





  do {
    wva;
    wvb;
    wo;
    #;
    wvc;
    wa;
    wvd;
    wo;
    wve;
    wa;
    @0;
    wvd;
    wo;
    @0;
    wve;
    wo;
    wa;
    @0;
    wva;
    wvd;
    wo;
    wvb;
    wve;
    wo;
    wa;
    wo;
    wva;
    wvb;
    wvc;
    wvd;
    wve;
    l42modlem2;
    wva;
    wvb;
    wvd;
    wve;
    l42modlem1;
    lbtr;
  };

  return $|- ( ( ( ( a v b ) ^ c ) v d ) ^ e ) =< ( ( a v b ) v ( ( a v d ) ^ ( b v e ) ) )$;
}
