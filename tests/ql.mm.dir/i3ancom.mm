include "wa.mm";
include "wi3.mm";
include "i3id.mm";
include "ancom.mm";
include "ri3.mm";
include "bi1.mm";
include "wwbmp.mm";

theorem i3ancom(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wva;
    wa;
    #;
    @0;
    wi3;
    #;
    wva;
    wvb;
    wa;
    #;
    @0;
    wi3;
    #;
    @0;
    i3id;
    @1;
    @3;
    @0;
    @2;
    @0;
    wvb;
    wva;
    ancom;
    ri3;
    bi1;
    wwbmp;
  };

  return $|-$ $( ( a ^ b ) ->3 ( b ^ a ) ) = 1$;
}
