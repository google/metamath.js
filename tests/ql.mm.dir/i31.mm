include "wt.mm";
include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "df-t.mm";
include "li3.mm";
include "bina3.mm";
include "ax-r2.mm";

theorem i31(wva: $term$ a) {





  do {
    wva;
    wt;
    wi3;
    wva;
    wva;
    wva;
    wn;
    #;
    wo;
    #;
    wi3;
    wt;
    wt;
    @1;
    wva;
    wva;
    df-t;
    li3;
    wva;
    @0;
    bina3;
    ax-r2;
  };

  return $|-$ $( a ->3 1 ) = 1$;
}
