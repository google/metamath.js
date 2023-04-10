include "df-le2.mm";
include "leoa.mm";

theorem df2le2(wva: $term$ a, wvb: $term$ b) {
  assume df2le2.1: $|- a =< b$;





  do {
    wva;
    wvb;
    wvb;
    wva;
    wvb;
    df2le2.1;
    df-le2;
    leoa;
  };

  return $|- ( a ^ b ) = a$;
}
