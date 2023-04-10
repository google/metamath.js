include "wo.mm";
include "wn.mm";
include "wa.mm";
include "anor3.mm";
include "ax-r1.mm";
include "comcom4.mm";
include "cbtr.mm";
include "gsth2.mm";
include "bctr.mm";
include "comcom5.mm";

theorem gstho(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume gstho.1: $|- b C c$;
  assume gstho.2: $|- a C ( b v c )$;





  do {
    wva;
    wvb;
    wo;
    #;
    wvc;
    @0;
    wn;
    #;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wa;
    #;
    wvc;
    wn;
    #;
    @4;
    @1;
    wva;
    wvb;
    anor3;
    ax-r1;
    @2;
    @3;
    @5;
    wvb;
    wvc;
    gstho.1;
    comcom4;
    @2;
    wvb;
    wvc;
    wo;
    #;
    wn;
    #;
    @3;
    @5;
    wa;
    #;
    wva;
    @6;
    gstho.2;
    comcom4;
    @8;
    @7;
    wvb;
    wvc;
    anor3;
    ax-r1;
    cbtr;
    gsth2;
    bctr;
    comcom5;
  };

  return $|- ( a v b ) C c$;
}
