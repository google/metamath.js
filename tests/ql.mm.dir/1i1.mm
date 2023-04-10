include "wt.mm";
include "wi1.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-i1.mm";
include "wf.mm";
include "df-f.mm";
include "ax-r1.mm";
include "ancom.mm";
include "an1.mm";
include "ax-r2.mm";
include "2or.mm";
include "ax-a2.mm";
include "or0.mm";

theorem 1i1(wva: $term$ a) {





  do {
    wt;
    wva;
    wi1;
    wt;
    wn;
    #;
    wt;
    wva;
    wa;
    #;
    wo;
    #;
    wva;
    wt;
    wva;
    df-i1;
    @2;
    wf;
    wva;
    wo;
    #;
    wva;
    @0;
    wf;
    @1;
    wva;
    wf;
    @0;
    df-f;
    ax-r1;
    @1;
    wva;
    wt;
    wa;
    wva;
    wt;
    wva;
    ancom;
    wva;
    an1;
    ax-r2;
    2or;
    @3;
    wva;
    wf;
    wo;
    wva;
    wf;
    wva;
    ax-a2;
    wva;
    or0;
    ax-r2;
    ax-r2;
    ax-r2;
  };

  return $|- ( 1 ->1 a ) = a$;
}
