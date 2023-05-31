include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wi1.mm";
include "u1lem9b.mm";
include "leran.mm";
include "letr.mm";

theorem oasr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume oasr.1: $|- ( ( a ->1 c ) ^ ( a v b ) ) =< c$;





  do {
    wva;
    wn;
    #;
    wva;
    wvb;
    wo;
    #;
    wa;
    wva;
    wvc;
    wi1;
    #;
    @1;
    wa;
    wvc;
    @0;
    @2;
    @1;
    wva;
    wvc;
    u1lem9b;
    leran;
    oasr.1;
    letr;
  };

  return $|-$ $( a ' ^ ( a v b ) ) =< c$;
}
