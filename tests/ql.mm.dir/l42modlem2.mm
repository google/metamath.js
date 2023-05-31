include "wo.mm";
include "wa.mm";
include "lea.mm";
include "leror.mm";
include "leor.mm";
include "le2an.mm";

theorem l42modlem2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d, wve: $term$ e) {





  do {
    wva;
    wvb;
    wo;
    #;
    wvc;
    wa;
    #;
    wvd;
    wo;
    @0;
    wvd;
    wo;
    wve;
    @0;
    wve;
    wo;
    @1;
    @0;
    wvd;
    @0;
    wvc;
    lea;
    leror;
    wve;
    @0;
    leor;
    le2an;
  };

  return $|-$ $( ( ( ( a v b ) ^ c ) v d ) ^ e ) =< ( ( ( a v b ) v d ) ^ ( ( a v b ) v e ) )$;
}
