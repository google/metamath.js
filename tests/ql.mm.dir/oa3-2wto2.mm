include "wa.mm";
include "wi1.mm";
include "wo.mm";
include "oas.mm";

theorem oa3-2wto2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume oa3-2wto2.1: $|- ( a ' ^ ( a v ( b ^ ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) =< c$;





  do {
    wva;
    wvb;
    wva;
    wvb;
    wa;
    wva;
    wvc;
    wi1;
    wvb;
    wvc;
    wi1;
    wa;
    wo;
    wa;
    wvc;
    oa3-2wto2.1;
    oas;
  };

  return $|-$ $( ( a ->1 c ) ^ ( a v ( b ^ ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) ) ) =< c$;
}
