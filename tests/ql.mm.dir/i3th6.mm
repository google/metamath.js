include "wi3.mm";
include "tb.mm";
include "i3abs1.mm";
include "bi1.mm";
include "bii3.mm";
include "skmp3.mm";

theorem i3th6(wva: $term$ a, wvb: $term$ b) {





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
    tb;
    @1;
    @0;
    wi3;
    @1;
    @0;
    wva;
    wvb;
    i3abs1;
    bi1;
    @1;
    @0;
    bii3;
    skmp3;
  };

  return $|- ( ( a ->3 ( a ->3 ( a ->3 b ) ) ) ->3 ( a ->3 ( a ->3 b ) ) ) = 1$;
}
