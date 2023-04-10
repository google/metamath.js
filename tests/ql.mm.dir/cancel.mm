include "wi1.mm";
include "wo.mm";
include "cancellem.mm";
include "ax-r1.mm";
include "lebi.mm";

theorem cancel(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume cancel.1: $|- ( ( d v ( a ->1 c ) ) ->1 c ) = ( ( d v ( b ->1 c ) ) ->1 c )$;





  do {
    wvd;
    wva;
    wvc;
    wi1;
    wo;
    #;
    wvd;
    wvb;
    wvc;
    wi1;
    wo;
    #;
    wva;
    wvb;
    wvc;
    wvd;
    cancel.1;
    cancellem;
    wvb;
    wva;
    wvc;
    wvd;
    @0;
    wvc;
    wi1;
    @1;
    wvc;
    wi1;
    cancel.1;
    ax-r1;
    cancellem;
    lebi;
  };

  return $|-$ $( d v ( a ->1 c ) ) = ( d v ( b ->1 c ) )$;
}
