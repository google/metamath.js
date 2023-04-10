include "wi1.mm";
include "wn.mm";
include "wa.mm";
include "wt.mm";
include "wf.mm";
include "wo.mm";
include "anor3.mm";
include "u1lemoa.mm";
include "ax-r4.mm";
include "ax-r2.mm";
include "df-f.mm";
include "ax-r1.mm";

theorem u1lemnana(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    #;
    wn;
    wva;
    wn;
    wa;
    #;
    wt;
    wn;
    #;
    wf;
    @1;
    @0;
    wva;
    wo;
    #;
    wn;
    @2;
    @0;
    wva;
    anor3;
    @3;
    wt;
    wva;
    wvb;
    u1lemoa;
    ax-r4;
    ax-r2;
    wf;
    @2;
    df-f;
    ax-r1;
    ax-r2;
  };

  return $|- ( ( a ->1 b ) ' ^ a ' ) = 0$;
}
