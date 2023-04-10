include "wt.mm";
include "wo.mm";
include "or1.mm";
include "bi1.mm";
include "wdf-le1.mm";

theorem wle1(wva: $term$ a) {





  do {
    wva;
    wt;
    wva;
    wt;
    wo;
    wt;
    wva;
    or1;
    bi1;
    wdf-le1;
  };

  return $|-$ $( a =<2 1 ) = 1$;
}
