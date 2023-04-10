include "i3le.mm";

theorem u3lemle2(wva: $term$ a, wvb: $term$ b) {
  assume u3lemle2.1: $|- ( a ->3 b ) = 1$;





  do {
    wva;
    wvb;
    u3lemle2.1;
    i3le;
  };

  return $|- a =< b$;
}
