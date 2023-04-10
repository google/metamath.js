include "wn.mm";
include "wi2.mm";
include "wi4.mm";
include "wa.mm";
include "wi5.mm";
include "negant2.mm";
include "negant4.mm";
include "2an.mm";
include "u24lem.mm";
include "3tr2.mm";

theorem negant5(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume negant.1: $|- ( a ->1 c ) = ( b ->1 c )$;





  do {
    wva;
    wn;
    #;
    wvc;
    wi2;
    #;
    @0;
    wvc;
    wi4;
    #;
    wa;
    wvb;
    wn;
    #;
    wvc;
    wi2;
    #;
    @3;
    wvc;
    wi4;
    #;
    wa;
    @0;
    wvc;
    wi5;
    @3;
    wvc;
    wi5;
    @1;
    @4;
    @2;
    @5;
    wva;
    wvb;
    wvc;
    negant.1;
    negant2;
    wva;
    wvb;
    wvc;
    negant.1;
    negant4;
    2an;
    @0;
    wvc;
    u24lem;
    @3;
    wvc;
    u24lem;
    3tr2;
  };

  return $|- ( a ' ->5 c ) = ( b ' ->5 c )$;
}
