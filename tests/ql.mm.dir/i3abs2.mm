include "wi3.mm";
include "i3abs1.mm";
include "bi1.mm";
include "wwbmp.mm";

theorem i3abs2(wva: $term$ a, wvb: $term$ b) {
  assume i3abs2.1: $|- ( a ->3 ( a ->3 ( a ->3 b ) ) ) = 1$;





  do {
    wva;
    wva;
    wva;
    wvb;
    wi3;
    wi3;
    #;
    wi3;
    #;
    @0;
    i3abs2.1;
    @1;
    @0;
    wva;
    wvb;
    i3abs1;
    bi1;
    wwbmp;
  };

  return $|-$ $( a ->3 ( a ->3 b ) ) = 1$;
}
