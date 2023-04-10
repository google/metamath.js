include "wa.mm";
include "lan.mm";
include "ran.mm";
include "ax-r2.mm";

theorem 2an(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume 2an.1: $|- a = b$;
  assume 2an.2: $|- c = d$;





  do {
    wva;
    wvc;
    wa;
    wva;
    wvd;
    wa;
    wvb;
    wvd;
    wa;
    wvc;
    wvd;
    wva;
    2an.2;
    lan;
    wva;
    wvb;
    wvd;
    2an.1;
    ran;
    ax-r2;
  };

  return $|- ( a ^ c ) = ( b ^ d )$;
}
