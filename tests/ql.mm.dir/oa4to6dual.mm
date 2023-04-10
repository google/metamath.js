include "wa.mm";
include "wo.mm";
include "wi1.mm";
include "oa4to6lem4.mm";
include "letr.mm";

theorem oa4to6dual(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d, wve: $term$ e, wvf: $term$ f, wvg: $term$ g) {
  assume oa4to6lem.1: $|- a ' =< b$;
  assume oa4to6lem.2: $|- c ' =< d$;
  assume oa4to6lem.3: $|- e ' =< f$;
  assume oa4to6lem.4: $|- g = ( ( ( a ^ b ) v ( c ^ d ) ) v ( e ^ f ) )$;
  assume oa4to6lem.oa4: $|- ( ( a ->1 g ) ^ ( a v ( c ^ ( ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^ ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) ) =< g$;





  do {
    wvb;
    wva;
    wvc;
    wva;
    wvc;
    wa;
    #;
    wvb;
    wvd;
    wa;
    wo;
    wva;
    wve;
    wa;
    #;
    wvb;
    wvf;
    wa;
    wo;
    wvc;
    wve;
    wa;
    #;
    wvd;
    wvf;
    wa;
    wo;
    wa;
    wo;
    wa;
    wo;
    wa;
    wva;
    wvg;
    wi1;
    #;
    wva;
    wvc;
    @0;
    @3;
    wvc;
    wvg;
    wi1;
    #;
    wa;
    wo;
    @1;
    @3;
    wve;
    wvg;
    wi1;
    #;
    wa;
    wo;
    @2;
    @4;
    @5;
    wa;
    wo;
    wa;
    wo;
    wa;
    wo;
    wa;
    wvg;
    wva;
    wvb;
    wvc;
    wvd;
    wve;
    wvf;
    wvg;
    oa4to6lem.1;
    oa4to6lem.2;
    oa4to6lem.3;
    oa4to6lem.4;
    oa4to6lem4;
    oa4to6lem.oa4;
    letr;
  };

  return $|-$ $( b ^ ( a v ( c ^ ( ( ( a ^ c ) v ( b ^ d ) ) v ( ( ( a ^ e ) v ( b ^ f ) ) ^ ( ( c ^ e ) v ( d ^ f ) ) ) ) ) ) ) =< g$;
}
