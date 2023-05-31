include "wi3.mm";
include "wn.mm";
include "i3id.mm";
include "ax-a1.mm";
include "li3.mm";
include "bi1.mm";
include "wwbmp.mm";

theorem bina1(wva: $term$ a) {





  do {
    wva;
    wva;
    wi3;
    #;
    wva;
    wva;
    wn;
    wn;
    #;
    wi3;
    #;
    wva;
    i3id;
    @0;
    @2;
    wva;
    @1;
    wva;
    wva;
    ax-a1;
    li3;
    bi1;
    wwbmp;
  };

  return $|-$ $( a ->3 a ' ' ) = 1$;
}
