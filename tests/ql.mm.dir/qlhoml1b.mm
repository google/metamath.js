include "wn.mm";
include "ax-a1.mm";
include "ax-r1.mm";
include "bile.mm";

theorem qlhoml1b(wva: $term$ a) {





  do {
    wva;
    wn;
    wn;
    #;
    wva;
    wva;
    @0;
    wva;
    ax-a1;
    ax-r1;
    bile;
  };

  return $|-$ $a ' ' =< a$;
}
