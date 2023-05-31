include "wo.mm";
include "wa.mm";
include "id.mm";
include "bile.mm";
include "ler2an.mm";
include "letr.mm";

theorem str(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume str.1: $|- a =< ( b v c )$;
  assume str.2: $|- ( a ^ ( b v c ) ) =< b$;





  do {
    wva;
    wva;
    wvb;
    wvc;
    wo;
    #;
    wa;
    wvb;
    wva;
    wva;
    @0;
    wva;
    wva;
    wva;
    id;
    bile;
    str.1;
    ler2an;
    str.2;
    letr;
  };

  return $|-$ $a =< b$;
}
