include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wi0.mm";
include "wi2.mm";
include "leid.mm";
include "leor.mm";
include "leao1.mm";
include "lel2or.mm";
include "leo.mm";
include "lebi.mm";
include "df-i0.mm";
include "df-i2.mm";
include "2or.mm";
include "3tr1.mm";

theorem lem4.6.6i0j2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wo;
    #;
    wvb;
    @0;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wo;
    #;
    @1;
    wva;
    wvb;
    wi0;
    #;
    wva;
    wvb;
    wi2;
    #;
    wo;
    @6;
    @5;
    @1;
    @1;
    @1;
    @4;
    @1;
    leid;
    wvb;
    @1;
    @3;
    wvb;
    @0;
    leor;
    @0;
    @2;
    wvb;
    leao1;
    lel2or;
    lel2or;
    @1;
    @4;
    leo;
    lebi;
    @6;
    @1;
    @7;
    @4;
    wva;
    wvb;
    df-i0;
    #;
    wva;
    wvb;
    df-i2;
    2or;
    @8;
    3tr1;
  };

  return $|-$ $( ( a ->0 b ) v ( a ->2 b ) ) = ( a ->0 b )$;
}
