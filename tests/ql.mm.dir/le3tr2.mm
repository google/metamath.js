include "ax-r1.mm";
include "le3tr1.mm";

theorem le3tr2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume le3tr2.1: $|- a =< b$;
  assume le3tr2.2: $|- a = c$;
  assume le3tr2.3: $|- b = d$;





  do {
    wva;
    wvb;
    wvc;
    wvd;
    le3tr2.1;
    wva;
    wvc;
    le3tr2.2;
    ax-r1;
    wvb;
    wvd;
    le3tr2.3;
    ax-r1;
    le3tr1;
  };

  return $|-$ $c =< d$;
}
