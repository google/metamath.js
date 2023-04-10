include "wn.mm";
include "ax-a1.mm";
include "lbtr.mm";
include "lecon1.mm";

theorem lecon2(wva: $term$ a, wvb: $term$ b) {
  assume lecon2.1: $|- a ' =< b$;





  do {
    wva;
    wvb;
    wn;
    #;
    wva;
    wn;
    wvb;
    @0;
    wn;
    lecon2.1;
    wvb;
    ax-a1;
    lbtr;
    lecon1;
  };

  return $|- b ' =< a$;
}
