include "wo.mm";
include "wid0.mm";
include "wi2.mm";
include "wn.mm";
include "wa.mm";
include "ancom.mm";
include "df-id0.mm";
include "3tr1.mm";
include "nom50.mm";
include "ax-r2.mm";

theorem nom60(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wva;
    wvb;
    wo;
    #;
    wid0;
    #;
    @0;
    wvb;
    wid0;
    #;
    wva;
    wvb;
    wi2;
    wvb;
    wn;
    @0;
    wo;
    #;
    @0;
    wn;
    wvb;
    wo;
    #;
    wa;
    @4;
    @3;
    wa;
    @1;
    @2;
    @3;
    @4;
    ancom;
    wvb;
    @0;
    df-id0;
    @0;
    wvb;
    df-id0;
    3tr1;
    wva;
    wvb;
    nom50;
    ax-r2;
  };

  return $|-$ $( b ==0 ( a v b ) ) = ( a ->2 b )$;
}
