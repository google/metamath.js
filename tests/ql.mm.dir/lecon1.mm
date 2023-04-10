include "wn.mm";
include "lecon.mm";
include "ax-a1.mm";
include "le3tr1.mm";

theorem lecon1(wva: $term$ a, wvb: $term$ b) {
  assume lecon1.1: $|- a ' =< b '$;





  do {
    wvb;
    wn;
    #;
    wn;
    wva;
    wn;
    #;
    wn;
    wvb;
    wva;
    @1;
    @0;
    lecon1.1;
    lecon;
    wvb;
    ax-a1;
    wva;
    ax-a1;
    le3tr1;
  };

  return $|- b =< a$;
}
