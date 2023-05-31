include "wn.mm";
include "wo.mm";
include "wi3.mm";
include "wi1.mm";
include "wi4.mm";
include "wi2.mm";
include "wa.mm";
include "ancom.mm";
include "anor3.mm";
include "ax-r2.mm";
include "ud3lem0a.mm";
include "ax-r1.mm";
include "nom13.mm";
include "i4i3.mm";
include "i2i1.mm";
include "3tr1.mm";

theorem nom44(wva: $term$ a, wvb: $term$ b) {





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
    wi3;
    #;
    @0;
    wva;
    wn;
    #;
    wi1;
    #;
    @1;
    wvb;
    wi4;
    wva;
    wvb;
    wi2;
    @3;
    @0;
    @0;
    @4;
    wa;
    #;
    wi3;
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
    ud3lem0a;
    ax-r1;
    @0;
    @4;
    nom13;
    ax-r2;
    @1;
    wvb;
    i4i3;
    wva;
    wvb;
    i2i1;
    3tr1;
  };

  return $|-$ $( ( a v b ) ->4 b ) = ( a ->2 b )$;
}
