include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wi0.mm";
include "wi1.mm";
include "id.mm";
include "df-i0.mm";
include "df-i1.mm";
include "3tr1.mm";

theorem nom10(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    @1;
    wva;
    @0;
    wi0;
    wva;
    wvb;
    wi1;
    @1;
    id;
    wva;
    @0;
    df-i0;
    wva;
    wvb;
    df-i1;
    3tr1;
  };

  return $|-$ $( a ->0 ( a ^ b ) ) = ( a ->1 b )$;
}
