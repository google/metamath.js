include "wa.mm";
include "wid0.mm";
include "wi1.mm";
include "wn.mm";
include "wo.mm";
include "ancom.mm";
include "df-id0.mm";
include "3tr1.mm";
include "nom20.mm";
include "ax-r2.mm";

theorem nom30(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wid0;
    #;
    wva;
    @0;
    wid0;
    #;
    wva;
    wvb;
    wi1;
    @0;
    wn;
    wva;
    wo;
    #;
    wva;
    wn;
    @0;
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
    @0;
    wva;
    df-id0;
    wva;
    @0;
    df-id0;
    3tr1;
    wva;
    wvb;
    nom20;
    ax-r2;
  };

  return $|- ( ( a ^ b ) ==0 a ) = ( a ->1 b )$;
}
