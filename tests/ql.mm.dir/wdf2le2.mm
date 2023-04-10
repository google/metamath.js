include "wdf-le2.mm";
include "wleoa.mm";

theorem wdf2le2(wva: $term$ a, wvb: $term$ b) {
  assume wdf2le2.1: $|- ( a =<2 b ) = 1$;





  do {
    wva;
    wvb;
    wvb;
    wva;
    wvb;
    wdf2le2.1;
    wdf-le2;
    wleoa;
  };

  return $|- ( ( a ^ b ) == a ) = 1$;
}
