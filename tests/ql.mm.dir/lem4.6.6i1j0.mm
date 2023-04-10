include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wi1.mm";
include "wi0.mm";
include "lear.mm";
include "lelor.mm";
include "df-le2.mm";
include "df-i1.mm";
include "df-i0.mm";
include "2or.mm";
include "3tr1.mm";

theorem lem4.6.6i1j0(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    @0;
    wvb;
    wo;
    #;
    wo;
    @3;
    wva;
    wvb;
    wi1;
    #;
    wva;
    wvb;
    wi0;
    #;
    wo;
    @5;
    @2;
    @3;
    @1;
    wvb;
    @0;
    wva;
    wvb;
    lear;
    lelor;
    df-le2;
    @4;
    @2;
    @5;
    @3;
    wva;
    wvb;
    df-i1;
    wva;
    wvb;
    df-i0;
    #;
    2or;
    @6;
    3tr1;
  };

  return $|-$ $( ( a ->1 b ) v ( a ->0 b ) ) = ( a ->0 b )$;
}
