include "axoa4.mm";
include "oa4ctob.mm";

theorem axoa4b(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {





  do {
    wva;
    wvb;
    wvc;
    wvd;
    wva;
    wvb;
    wvc;
    wvd;
    axoa4;
    oa4ctob;
  };

  return $|-$ $( ( a ->1 d ) ^ ( a v ( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =< d$;
}
