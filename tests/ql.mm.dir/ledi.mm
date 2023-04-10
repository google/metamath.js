include "wa.mm";
include "wo.mm";
include "anidm.mm";
include "ax-r1.mm";
include "lea.mm";
include "le2or.mm";
include "oridm.mm";
include "lbtr.mm";
include "ancom.mm";
include "bltr.mm";
include "le2an.mm";

theorem ledi(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wvc;
    wa;
    #;
    wo;
    #;
    @2;
    @2;
    wa;
    #;
    wva;
    wvb;
    wvc;
    wo;
    #;
    wa;
    @3;
    @2;
    @2;
    anidm;
    ax-r1;
    @2;
    wva;
    @2;
    @4;
    @2;
    wva;
    wva;
    wo;
    wva;
    @0;
    wva;
    @1;
    wva;
    wva;
    wvb;
    lea;
    wva;
    wvc;
    lea;
    le2or;
    wva;
    oridm;
    lbtr;
    @0;
    wvb;
    @1;
    wvc;
    @0;
    wvb;
    wva;
    wa;
    wvb;
    wva;
    wvb;
    ancom;
    wvb;
    wva;
    lea;
    bltr;
    @1;
    wvc;
    wva;
    wa;
    wvc;
    wva;
    wvc;
    ancom;
    wvc;
    wva;
    lea;
    bltr;
    le2or;
    le2an;
    bltr;
  };

  return $|- ( ( a ^ b ) v ( a ^ c ) ) =< ( a ^ ( b v c ) )$;
}
