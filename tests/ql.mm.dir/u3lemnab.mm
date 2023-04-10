include "wi3.mm";
include "wn.mm";
include "wa.mm";
include "wf.mm";
include "wo.mm";
include "wt.mm";
include "u3lemonb.mm";
include "oran1.mm";
include "df-f.mm";
include "con2.mm";
include "ax-r1.mm";
include "3tr2.mm";
include "con1.mm";

theorem u3lemnab(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    wn;
    wvb;
    wa;
    #;
    wf;
    @0;
    wvb;
    wn;
    wo;
    wt;
    @1;
    wn;
    wf;
    wn;
    #;
    wva;
    wvb;
    u3lemonb;
    @0;
    wvb;
    oran1;
    @2;
    wt;
    wf;
    wt;
    df-f;
    con2;
    ax-r1;
    3tr2;
    con1;
  };

  return $|- ( ( a ->3 b ) ' ^ b ) = 0$;
}
