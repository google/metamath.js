include "wn.mm";
include "wo.mm";
include "ax-a5.mm";
include "bi1.mm";

theorem wa5(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wn;
    wvb;
    wn;
    #;
    wo;
    wn;
    wo;
    wva;
    wva;
    @0;
    ax-a5;
    bi1;
  };

  return $|- ( ( a v ( a ' v b ' ) ' ) == a ) = 1$;
}
