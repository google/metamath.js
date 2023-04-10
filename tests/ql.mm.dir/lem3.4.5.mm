include "wo.mm";
include "lem3.3.5.mm";
include "2vwomr1a.mm";

theorem lem3.4.5(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume lem3.4.5.1: $|- ( a ==5 b ) = 1$;





  do {
    wva;
    wvb;
    wvc;
    wo;
    wva;
    wvb;
    wvc;
    lem3.4.5.1;
    lem3.3.5;
    2vwomr1a;
  };

  return $|-$ $( a ->2 ( b v c ) ) = 1$;
}
