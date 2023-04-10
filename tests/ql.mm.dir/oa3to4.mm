include "lecon3.mm";
include "oa3to4lem6.mm";
include "oa3to4lem5.mm";

theorem oa3to4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d, wve: $term$ e, wvf: $term$ f, wvg: $term$ g) {
  assume oa3to4.oa4.1: $|- a =< b '$;
  assume oa3to4.oa4.2: $|- c =< d '$;
  assume oa3to4.3: $|- g = ( ( b ' ^ a ' ) v ( d ' ^ c ' ) )$;
  assume oa3to4.4: $|- e = b '$;
  assume oa3to4.5: $|- f = d '$;
  assume oa3to4.oa3: $|- ( e ^ ( ( e ->1 g ) v ( ( f ->1 g ) ^ ( ( e ^ f ) v ( ( e ->1 g ) ^ ( f ->1 g ) ) ) ) ) ) =< ( ( e ^ g ) v ( f ^ g ) )$;





  do {
    wvb;
    wva;
    wvd;
    wvc;
    wvb;
    wva;
    wvd;
    wvc;
    wve;
    wvf;
    wvg;
    wva;
    wvb;
    oa3to4.oa4.1;
    lecon3;
    wvc;
    wvd;
    oa3to4.oa4.2;
    lecon3;
    oa3to4.3;
    oa3to4.4;
    oa3to4.5;
    oa3to4.oa3;
    oa3to4lem6;
    oa3to4lem5;
  };

  return $|- ( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v ( ( a v c ) ^ ( b v d ) ) ) ) )$;
}
