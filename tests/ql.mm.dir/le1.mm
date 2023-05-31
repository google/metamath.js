include "wt.mm";
include "or1.mm";
include "df-le1.mm";

theorem le1(wva: $term$ a) {





  do {
    wva;
    wt;
    wva;
    or1;
    df-le1;
  };

  return $|-$ $a =< 1$;
}
