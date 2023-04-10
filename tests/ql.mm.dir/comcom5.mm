include "wn.mm";
include "wa.mm";
include "wo.mm";
include "comcom4.mm";
include "df-c2.mm";
include "ax-a1.mm";
include "2an.mm";
include "2or.mm";
include "3tr1.mm";
include "df-c1.mm";

theorem comcom5(wva: $term$ a, wvb: $term$ b) {
  assume comcom5.1: $|- a ' C b '$;





  do {
    wva;
    wvb;
    wva;
    wn;
    #;
    wn;
    #;
    @1;
    wvb;
    wn;
    #;
    wn;
    #;
    wa;
    #;
    @1;
    @3;
    wn;
    #;
    wa;
    #;
    wo;
    wva;
    wva;
    wvb;
    wa;
    #;
    wva;
    @2;
    wa;
    #;
    wo;
    @1;
    @3;
    @0;
    @2;
    comcom5.1;
    comcom4;
    df-c2;
    wva;
    ax-a1;
    #;
    @7;
    @4;
    @8;
    @6;
    wva;
    @1;
    wvb;
    @3;
    @9;
    wvb;
    ax-a1;
    2an;
    wva;
    @1;
    @2;
    @5;
    @9;
    @2;
    ax-a1;
    2an;
    2or;
    3tr1;
    df-c1;
  };

  return $|-$ $a C b$;
}
