include "wo.mm";
include "leo.mm";
include "ax-a2.mm";
include "lbtr.mm";

theorem leor(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wo;
    wvb;
    wva;
    wo;
    wva;
    wvb;
    leo;
    wva;
    wvb;
    ax-a2;
    lbtr;
  };

  return $|-$ $a =< ( b v a )$;
}
