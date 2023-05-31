include "wn.mm";
include "wi1.mm";
include "u1lem9a.mm";
include "u1lem9b.mm";
include "letr.mm";

theorem u1lem9ab(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wi1;
    wn;
    @0;
    wva;
    wvb;
    wi1;
    wva;
    wvb;
    u1lem9a;
    wva;
    wvb;
    u1lem9b;
    letr;
  };

  return $|-$ $( a ' ->1 b ) ' =< ( a ->1 b )$;
}
