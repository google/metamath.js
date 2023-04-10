include "wo.mm";
include "lecom.mm";
include "comcom.mm";
include "wn.mm";
include "comcom7.mm";
include "com2or.mm";
include "bctr.mm";

theorem gt1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume gt1.1: $|- a = ( b v c )$;
  assume gt1.2: $|- b =< d$;
  assume gt1.3: $|- c =< d '$;





  do {
    wva;
    wvb;
    wvc;
    wo;
    #;
    wvd;
    gt1.1;
    wvd;
    @0;
    wvd;
    wvb;
    wvc;
    wvb;
    wvd;
    wvb;
    wvd;
    gt1.2;
    lecom;
    comcom;
    wvc;
    wvd;
    wvc;
    wvd;
    wvc;
    wvd;
    wn;
    gt1.3;
    lecom;
    comcom7;
    comcom;
    com2or;
    comcom;
    bctr;
  };

  return $|- a C d$;
}
