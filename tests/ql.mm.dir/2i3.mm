include "wi3.mm";
include "li3.mm";
include "ri3.mm";
include "ax-r2.mm";

theorem 2i3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume 2i3.1: $|- a = b$;
  assume 2i3.2: $|- c = d$;





  do {
    wva;
    wvc;
    wi3;
    wva;
    wvd;
    wi3;
    wvb;
    wvd;
    wi3;
    wvc;
    wvd;
    wva;
    2i3.2;
    li3;
    wva;
    wvb;
    wvd;
    2i3.1;
    ri3;
    ax-r2;
  };

  return $|-$ $( a ->3 c ) = ( b ->3 d )$;
}
