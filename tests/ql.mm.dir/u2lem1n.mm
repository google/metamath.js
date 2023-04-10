include "wi2.mm";
include "u2lem1.mm";
include "ax-r4.mm";

theorem u2lem1n(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi2;
    wva;
    wi2;
    wva;
    wva;
    wvb;
    u2lem1;
    ax-r4;
  };

  return $|-$ $( ( a ->2 b ) ->2 a ) ' = a '$;
}
