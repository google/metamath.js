include "bi3tr.mm";
include "ax-r1.mm";
include "i3btr.mm";

theorem i33tr1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume i33tr1.1: $|- ( a ->3 b ) = 1$;
  assume i33tr1.2: $|- c = a$;
  assume i33tr1.3: $|- d = b$;





  do {
    wvc;
    wvb;
    wvd;
    wvc;
    wva;
    wvb;
    i33tr1.2;
    i33tr1.1;
    bi3tr;
    wvd;
    wvb;
    i33tr1.3;
    ax-r1;
    i3btr;
  };

  return $|- ( c ->3 d ) = 1$;
}
