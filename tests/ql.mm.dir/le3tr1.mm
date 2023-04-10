include "bltr.mm";
include "ax-r1.mm";
include "lbtr.mm";

theorem le3tr1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume le3tr1.1: $|- a =< b$;
  assume le3tr1.2: $|- c = a$;
  assume le3tr1.3: $|- d = b$;





  do {
    wvc;
    wvb;
    wvd;
    wvc;
    wva;
    wvb;
    le3tr1.2;
    le3tr1.1;
    bltr;
    wvd;
    wvb;
    le3tr1.3;
    ax-r1;
    lbtr;
  };

  return $|- c =< d$;
}
