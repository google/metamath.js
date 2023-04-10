include "wf.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "ax-r1.mm";
include "ancom.mm";
include "ax-r2.mm";
include "lor.mm";
include "or0.mm";
include "oml2.mm";
include "3tr2.mm";

theorem oml3(wva: $term$ a, wvb: $term$ b) {
  assume oml3.1: $|- a =< b$;
  assume oml3.2: $|- ( b ^ a ' ) = 0$;





  do {
    wva;
    wf;
    wo;
    wva;
    wva;
    wn;
    #;
    wvb;
    wa;
    #;
    wo;
    wva;
    wvb;
    wf;
    @1;
    wva;
    wf;
    wvb;
    @0;
    wa;
    #;
    @1;
    @2;
    wf;
    oml3.2;
    ax-r1;
    wvb;
    @0;
    ancom;
    ax-r2;
    lor;
    wva;
    or0;
    wva;
    wvb;
    oml3.1;
    oml2;
    3tr2;
  };

  return $|- a = b$;
}
