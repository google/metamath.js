include "wi1.mm";
include "wa.mm";
include "wo.mm";
include "lear.mm";
include "lel2or.mm";
include "letr.mm";

theorem oa4b(wva: $term$ a, wvc: $term$ c, wve: $term$ e, wvg: $term$ g) {
  assume oa4b.1: $|- ( ( a ->1 g ) ^ ( a v ( c ^ ( ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^ ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) ) =< ( ( ( a ^ g ) v ( c ^ g ) ) v ( e ^ g ) )$;





  do {
    wva;
    wvg;
    wi1;
    #;
    wva;
    wvc;
    wva;
    wvc;
    wa;
    @0;
    wvc;
    wvg;
    wi1;
    #;
    wa;
    wo;
    wva;
    wve;
    wa;
    @0;
    wve;
    wvg;
    wi1;
    #;
    wa;
    wo;
    wvc;
    wve;
    wa;
    @1;
    @2;
    wa;
    wo;
    wa;
    wo;
    wa;
    wo;
    wa;
    wva;
    wvg;
    wa;
    #;
    wvc;
    wvg;
    wa;
    #;
    wo;
    #;
    wve;
    wvg;
    wa;
    #;
    wo;
    wvg;
    oa4b.1;
    @5;
    wvg;
    @6;
    @3;
    wvg;
    @4;
    wva;
    wvg;
    lear;
    wvc;
    wvg;
    lear;
    lel2or;
    wve;
    wvg;
    lear;
    lel2or;
    letr;
  };

  return $|- ( ( a ->1 g ) ^ ( a v ( c ^ ( ( ( a ^ c ) v ( ( a ->1 g ) ^ ( c ->1 g ) ) ) v ( ( ( a ^ e ) v ( ( a ->1 g ) ^ ( e ->1 g ) ) ) ^ ( ( c ^ e ) v ( ( c ->1 g ) ^ ( e ->1 g ) ) ) ) ) ) ) ) =< g$;
}
