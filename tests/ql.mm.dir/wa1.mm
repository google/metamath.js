include "wn.mm";
include "ax-a1.mm";
include "bi1.mm";

theorem wa1(wva: $term$ a) {





  do {
    wva;
    wva;
    wn;
    wn;
    wva;
    ax-a1;
    bi1;
  };

  return $|-$ $( a == a ' ' ) = 1$;
}
