include "tb.mm";
include "wo.mm";
include "wa.mm";
include "wi1.mm";
include "mlaconj.mm";
include "letr.mm";

theorem mlaconj2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume mlaconj2.1: $|- ( ( ( ( a ->1 ( a ^ b ) ) ^ ( ( a ^ b ) ->1 ( ( a ^ b ) v c ) ) ) ^ ( ( ( ( a ^ b ) v c ) ->1 c ) ^ ( c ->1 ( a v b ) ) ) ) ^ ( ( a v b ) ->1 a ) ) =< ( a == c )$;





  do {
    wva;
    wvb;
    tb;
    wva;
    wvc;
    tb;
    #;
    wvb;
    wvc;
    tb;
    wo;
    wa;
    wva;
    wva;
    wvb;
    wa;
    #;
    wi1;
    @1;
    @1;
    wvc;
    wo;
    #;
    wi1;
    wa;
    @2;
    wvc;
    wi1;
    wvc;
    wva;
    wvb;
    wo;
    #;
    wi1;
    wa;
    wa;
    @3;
    wva;
    wi1;
    wa;
    @0;
    wva;
    wvb;
    wvc;
    mlaconj;
    mlaconj2.1;
    letr;
  };

  return $|- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) =< ( a == c )$;
}
