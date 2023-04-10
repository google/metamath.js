include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wi0.mm";
include "wi3.mm";
include "leid.mm";
include "leao1.mm";
include "lel2or.mm";
include "lear.mm";
include "leo.mm";
include "lebi.mm";
include "df-i0.mm";
include "df-i3.mm";
include "2or.mm";
include "3tr1.mm";

theorem lem4.6.6i0j3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wo;
    #;
    @0;
    wvb;
    wa;
    #;
    @0;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wva;
    @1;
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
    wi3;
    #;
    wo;
    @9;
    @8;
    @1;
    @1;
    @1;
    @7;
    @1;
    leid;
    @5;
    @1;
    @6;
    @2;
    @1;
    @4;
    @0;
    wvb;
    wvb;
    leao1;
    @0;
    @3;
    wvb;
    leao1;
    lel2or;
    wva;
    @1;
    lear;
    lel2or;
    lel2or;
    @1;
    @7;
    leo;
    lebi;
    @9;
    @1;
    @10;
    @7;
    wva;
    wvb;
    df-i0;
    #;
    wva;
    wvb;
    df-i3;
    2or;
    @11;
    3tr1;
  };

  return $|-$ $( ( a ->0 b ) v ( a ->3 b ) ) = ( a ->0 b )$;
}
