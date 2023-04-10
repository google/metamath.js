include "wa.mm";
include "wf.mm";
include "wn.mm";
include "lecon3.mm";
include "lelan.mm";
include "dff.mm";
include "ax-r1.mm";
include "lbtr.mm";
include "le0.mm";
include "lebi.mm";

theorem ortha(wva: $term$ a, wvb: $term$ b) {
  assume ortha.1: $|- a =< b '$;





  do {
    wva;
    wvb;
    wa;
    #;
    wf;
    @0;
    wva;
    wva;
    wn;
    #;
    wa;
    #;
    wf;
    wvb;
    @1;
    wva;
    wva;
    wvb;
    ortha.1;
    lecon3;
    lelan;
    wf;
    @2;
    wva;
    dff;
    ax-r1;
    lbtr;
    @0;
    le0;
    lebi;
  };

  return $|-$ $( a ^ b ) = 0$;
}
