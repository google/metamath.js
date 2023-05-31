include "wt.mm";
include "wo.mm";
include "ax-a2.mm";
include "or1.mm";
include "ax-r2.mm";

theorem or1r(wva: $term$ a) {





  do {
    wt;
    wva;
    wo;
    wva;
    wt;
    wo;
    wt;
    wt;
    wva;
    ax-a2;
    wva;
    or1;
    ax-r2;
  };

  return $|-$ $( 1 v a ) = 1$;
}
