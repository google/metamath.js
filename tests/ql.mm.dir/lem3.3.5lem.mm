include "wt.mm";
include "le1.mm";
include "lebi.mm";

theorem lem3.3.5lem(wva: $term$ a) {
  assume lem3.3.5lem.1: $|- 1 =< a$;





  do {
    wva;
    wt;
    wva;
    le1;
    lem3.3.5lem.1;
    lebi;
  };

  return $|-$ $a = 1$;
}
