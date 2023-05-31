include "leao.mm";
include "df-le1.mm";

theorem df2le1(wva: $term$ a, wvb: $term$ b) {
  assume df2le1.1: $|- ( a ^ b ) = a$;





  do {
    wva;
    wvb;
    wva;
    wvb;
    wva;
    df2le1.1;
    leao;
    df-le1;
  };

  return $|-$ $a =< b$;
}
