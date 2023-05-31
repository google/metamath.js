include "wi1.mm";
include "u1lem1.mm";
include "ax-r4.mm";

theorem u1lem1n(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    wva;
    wi1;
    wva;
    wva;
    wvb;
    u1lem1;
    ax-r4;
  };

  return $|-$ $( ( a ->1 b ) ->1 a ) ' = a '$;
}
