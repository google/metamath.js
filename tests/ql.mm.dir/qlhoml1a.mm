include "wn.mm";
include "ax-a1.mm";
include "bile.mm";

theorem qlhoml1a(wva: $term$ a) {





  do {
    wva;
    wva;
    wn;
    wn;
    wva;
    ax-a1;
    bile;
  };

  return $|- a =< a ' '$;
}
