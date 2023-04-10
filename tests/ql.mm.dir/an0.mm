include "wf.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "df-a.mm";
include "wt.mm";
include "or1.mm";
include "df-f.mm";
include "con2.mm";
include "lor.mm";
include "3tr1.mm";
include "ax-r2.mm";

theorem an0(wva: $term$ a) {





  do {
    wva;
    wf;
    wa;
    wva;
    wn;
    #;
    wf;
    wn;
    #;
    wo;
    #;
    wn;
    wf;
    wva;
    wf;
    df-a;
    @2;
    wf;
    @0;
    wt;
    wo;
    wt;
    @2;
    @1;
    @0;
    or1;
    @1;
    wt;
    @0;
    wf;
    wt;
    df-f;
    con2;
    #;
    lor;
    @3;
    3tr1;
    con2;
    ax-r2;
  };

  return $|- ( a ^ 0 ) = 0$;
}
