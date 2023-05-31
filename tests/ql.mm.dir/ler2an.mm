include "wa.mm";
include "anidm.mm";
include "ax-r1.mm";
include "le2an.mm";
include "bltr.mm";

theorem ler2an(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ler2.1: $|- a =< b$;
  assume ler2.2: $|- a =< c$;





  do {
    wva;
    wva;
    wva;
    wa;
    #;
    wvb;
    wvc;
    wa;
    @0;
    wva;
    wva;
    anidm;
    ax-r1;
    wva;
    wvb;
    wva;
    wvc;
    ler2.1;
    ler2.2;
    le2an;
    bltr;
  };

  return $|-$ $a =< ( b ^ c )$;
}
