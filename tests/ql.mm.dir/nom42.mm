include "wn.mm";
include "wo.mm";
include "wi1.mm";
include "wi2.mm";
include "wa.mm";
include "ancom.mm";
include "anor3.mm";
include "ax-r2.mm";
include "ud1lem0a.mm";
include "ax-r1.mm";
include "nom11.mm";
include "i2i1.mm";
include "3tr1.mm";

theorem nom42(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wn;
    #;
    wva;
    wvb;
    wo;
    #;
    wn;
    #;
    wi1;
    #;
    @0;
    wva;
    wn;
    #;
    wi1;
    #;
    @1;
    wvb;
    wi2;
    wva;
    wvb;
    wi2;
    @3;
    @0;
    @0;
    @4;
    wa;
    #;
    wi1;
    #;
    @5;
    @7;
    @3;
    @6;
    @2;
    @0;
    @6;
    @4;
    @0;
    wa;
    @2;
    @0;
    @4;
    ancom;
    wva;
    wvb;
    anor3;
    ax-r2;
    ud1lem0a;
    ax-r1;
    @0;
    @4;
    nom11;
    ax-r2;
    @1;
    wvb;
    i2i1;
    wva;
    wvb;
    i2i1;
    3tr1;
  };

  return $|- ( ( a v b ) ->2 b ) = ( a ->2 b )$;
}
