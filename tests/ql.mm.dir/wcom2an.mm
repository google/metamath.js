include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wcomcom4.mm";
include "wcom2or.mm";
include "df-a.mm";
include "con2.mm";
include "ax-r1.mm";
include "bi1.mm";
include "wcbtr.mm";
include "wcomcom5.mm";

theorem wcom2an(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wfh.1: $|- C ( a , b ) = 1$;
  assume wfh.2: $|- C ( a , c ) = 1$;





  do {
    wva;
    wvb;
    wvc;
    wa;
    #;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wvc;
    wn;
    #;
    wo;
    #;
    @0;
    wn;
    #;
    @1;
    @2;
    @3;
    wva;
    wvb;
    wfh.1;
    wcomcom4;
    wva;
    wvc;
    wfh.2;
    wcomcom4;
    wcom2or;
    @4;
    @5;
    @5;
    @4;
    @0;
    @4;
    wvb;
    wvc;
    df-a;
    con2;
    ax-r1;
    bi1;
    wcbtr;
    wcomcom5;
  };

  return $|-$ $C ( a , ( b ^ c ) ) = 1$;
}
