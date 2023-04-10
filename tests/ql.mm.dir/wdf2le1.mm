include "wleao.mm";
include "wdf-le1.mm";

theorem wdf2le1(wva: $term$ a, wvb: $term$ b) {
  assume wdf2le1.1: $|- ( ( a ^ b ) == a ) = 1$;





  do {
    wva;
    wvb;
    wva;
    wvb;
    wva;
    wdf2le1.1;
    wleao;
    wdf-le1;
  };

  return $|-$ $( a =<2 b ) = 1$;
}
