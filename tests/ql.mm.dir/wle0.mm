include "wf.mm";
include "wle2.mm";
include "wo.mm";
include "tb.mm";
include "wt.mm";
include "df-le.mm";
include "ax-a2.mm";
include "or0.mm";
include "ax-r2.mm";
include "bi1.mm";

theorem wle0(wva: $term$ a) {





  do {
    wf;
    wva;
    wle2;
    wf;
    wva;
    wo;
    #;
    wva;
    tb;
    wt;
    wf;
    wva;
    df-le;
    @0;
    wva;
    @0;
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
    bi1;
    ax-r2;
  };

  return $|- ( 0 =<2 a ) = 1$;
}
