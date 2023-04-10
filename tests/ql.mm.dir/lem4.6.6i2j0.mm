include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wi2.mm";
include "wi0.mm";
include "leor.mm";
include "leao1.mm";
include "lel2or.mm";
include "df-le2.mm";
include "df-i2.mm";
include "df-i0.mm";
include "2or.mm";
include "3tr1.mm";

theorem lem4.6.6i2j0(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    @0;
    wvb;
    wo;
    #;
    wo;
    @4;
    wva;
    wvb;
    wi2;
    #;
    wva;
    wvb;
    wi0;
    #;
    wo;
    @6;
    @3;
    @4;
    wvb;
    @4;
    @2;
    wvb;
    @0;
    leor;
    @0;
    @1;
    wvb;
    leao1;
    lel2or;
    df-le2;
    @5;
    @3;
    @6;
    @4;
    wva;
    wvb;
    df-i2;
    wva;
    wvb;
    df-i0;
    #;
    2or;
    @7;
    3tr1;
  };

  return $|- ( ( a ->2 b ) v ( a ->0 b ) ) = ( a ->0 b )$;
}
