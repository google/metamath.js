include "u1lem9a.mm";

theorem lem4.6.3le1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    u1lem9a;
  };

  return $|-$ $( a ' ->1 b ) ' =< a '$;
}
