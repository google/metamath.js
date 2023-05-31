include "wf.mm";
include "wo.mm";
include "wn.mm";
include "dff2.mm";
include "ax-a2.mm";
include "ax-r4.mm";
include "ax-r2.mm";
include "lor.mm";
include "ax-a5.mm";

theorem or0(wva: $term$ a) {





  do {
    wva;
    wf;
    wo;
    wva;
    wva;
    wn;
    #;
    wva;
    wo;
    #;
    wn;
    #;
    wo;
    wva;
    wf;
    @2;
    wva;
    wf;
    wva;
    @0;
    wo;
    #;
    wn;
    @2;
    wva;
    dff2;
    @3;
    @1;
    wva;
    @0;
    ax-a2;
    ax-r4;
    ax-r2;
    lor;
    wva;
    wva;
    ax-a5;
    ax-r2;
  };

  return $|-$ $( a v 0 ) = a$;
}
