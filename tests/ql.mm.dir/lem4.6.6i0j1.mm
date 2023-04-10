include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wi0.mm";
include "wi1.mm";
include "leid.mm";
include "lear.mm";
include "lelor.mm";
include "lel2or.mm";
include "leo.mm";
include "lebi.mm";
include "df-i0.mm";
include "df-i1.mm";
include "2or.mm";
include "3tr1.mm";

theorem lem4.6.6i0j1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wo;
    #;
    @0;
    wva;
    wvb;
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
    wi1;
    #;
    wo;
    @5;
    @4;
    @1;
    @1;
    @1;
    @3;
    @1;
    leid;
    @2;
    wvb;
    @0;
    wva;
    wvb;
    lear;
    lelor;
    lel2or;
    @1;
    @3;
    leo;
    lebi;
    @5;
    @1;
    @6;
    @3;
    wva;
    wvb;
    df-i0;
    #;
    wva;
    wvb;
    df-i1;
    2or;
    @7;
    3tr1;
  };

  return $|- ( ( a ->0 b ) v ( a ->1 b ) ) = ( a ->0 b )$;
}
