include "wi2.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "ax-a2.mm";
include "3vth1.mm";
include "df-le2.mm";
include "ax-r2.mm";

theorem 3vth3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvc;
    wi2;
    #;
    wva;
    wvb;
    wi2;
    wvb;
    wvc;
    wo;
    wn;
    wa;
    #;
    wo;
    @1;
    @0;
    wo;
    @0;
    @0;
    @1;
    ax-a2;
    @1;
    @0;
    wva;
    wvb;
    wvc;
    3vth1;
    df-le2;
    ax-r2;
  };

  return $|- ( ( a ->2 c ) v ( ( a ->2 b ) ^ ( b v c ) ' ) ) = ( a ->2 c )$;
}
