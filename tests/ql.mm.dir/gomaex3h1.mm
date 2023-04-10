include "wn.mm";
include "ax-r4.mm";
include "le3tr1.mm";

theorem gomaex3h1(wva: $term$ a, wvb: $term$ b, wvg: $term$ g, wvh: $term$ h) {
  assume gomaex3h1.1: $|- a =< b '$;
  assume gomaex3h1.12: $|- g = a$;
  assume gomaex3h1.13: $|- h = b$;





  do {
    wva;
    wvb;
    wn;
    wvg;
    wvh;
    wn;
    gomaex3h1.1;
    gomaex3h1.12;
    wvh;
    wvb;
    gomaex3h1.13;
    ax-r4;
    le3tr1;
  };

  return $|-$ $g =< h '$;
}
