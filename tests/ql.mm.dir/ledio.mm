include "wa.mm";
include "wo.mm";
include "anidm.mm";
include "ax-r1.mm";
include "leo.mm";
include "le2an.mm";
include "bltr.mm";
include "ax-a2.mm";
include "lbtr.mm";
include "le2or.mm";
include "oridm.mm";

theorem ledio(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wa;
    #;
    wo;
    wva;
    wvb;
    wo;
    #;
    wva;
    wvc;
    wo;
    #;
    wa;
    #;
    @3;
    wo;
    @3;
    wva;
    @3;
    @0;
    @3;
    wva;
    wva;
    wva;
    wa;
    #;
    @3;
    @4;
    wva;
    wva;
    anidm;
    ax-r1;
    wva;
    @1;
    wva;
    @2;
    wva;
    wvb;
    leo;
    wva;
    wvc;
    leo;
    le2an;
    bltr;
    wvb;
    @1;
    wvc;
    @2;
    wvb;
    wvb;
    wva;
    wo;
    @1;
    wvb;
    wva;
    leo;
    wvb;
    wva;
    ax-a2;
    lbtr;
    wvc;
    wvc;
    wva;
    wo;
    @2;
    wvc;
    wva;
    leo;
    wvc;
    wva;
    ax-a2;
    lbtr;
    le2an;
    le2or;
    @3;
    oridm;
    lbtr;
  };

  return $|-$ $( a v ( b ^ c ) ) =< ( ( a v b ) ^ ( a v c ) )$;
}
