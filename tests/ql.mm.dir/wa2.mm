include "wo.mm";
include "ax-a2.mm";
include "bi1.mm";

theorem wa2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wo;
    wvb;
    wva;
    wo;
    wva;
    wvb;
    ax-a2;
    bi1;
  };

  return $|- ( ( a v b ) == ( b v a ) ) = 1$;
}
