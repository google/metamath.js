include "wa.mm";
include "wo.mm";
include "ax-a2.mm";
include "orabs.mm";
include "ax-r2.mm";
include "df-le1.mm";

theorem lea(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    @0;
    wva;
    wo;
    wva;
    @0;
    wo;
    wva;
    @0;
    wva;
    ax-a2;
    wva;
    wvb;
    orabs;
    ax-r2;
    df-le1;
  };

  return $|- ( a ^ b ) =< a$;
}
