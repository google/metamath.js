include "wo.mm";
include "wi2.mm";
include "wn.mm";
include "wa.mm";
include "3vth7.mm";
include "ax-r1.mm";
include "3vth6.mm";
include "ax-r2.mm";

theorem 3vth8(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wo;
    #;
    wi2;
    #;
    wva;
    wvb;
    wi2;
    #;
    wn;
    @0;
    wi2;
    #;
    @2;
    wvc;
    wvb;
    wi2;
    wa;
    wva;
    wvc;
    wi2;
    wvb;
    wvc;
    wi2;
    wa;
    wo;
    @3;
    @1;
    wva;
    wvb;
    wvc;
    3vth7;
    ax-r1;
    wva;
    wvb;
    wvc;
    3vth6;
    ax-r2;
  };

  return $|- ( a ->2 ( b v c ) ) = ( ( ( a ->2 b ) ^ ( c ->2 b ) ) v ( ( a ->2 c ) ^ ( b ->2 c ) ) )$;
}
