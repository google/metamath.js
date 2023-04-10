include "wn.mm";
include "wo.mm";
include "ax-a4.mm";
include "bi1.mm";

theorem wa4(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wvb;
    wn;
    wo;
    #;
    wo;
    @0;
    wva;
    wvb;
    ax-a4;
    bi1;
  };

  return $|- ( ( a v ( b v b ' ) ) == ( b v b ' ) ) = 1$;
}
