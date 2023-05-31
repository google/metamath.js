include "wa.mm";
include "wn.mm";
include "wo.mm";
include "comcom4.mm";
include "com2or.mm";
include "df-a.mm";
include "con2.mm";
include "ax-r1.mm";
include "cbtr.mm";
include "comcom5.mm";

theorem com2an(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume fh.1: $|- a C b$;
  assume fh.2: $|- a C c$;





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
    fh.1;
    comcom4;
    wva;
    wvc;
    fh.2;
    comcom4;
    com2or;
    @5;
    @4;
    @0;
    @4;
    wvb;
    wvc;
    df-a;
    con2;
    ax-r1;
    cbtr;
    comcom5;
  };

  return $|-$ $a C ( b ^ c )$;
}
