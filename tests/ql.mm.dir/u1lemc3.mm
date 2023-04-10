include "comid.mm";
include "u1lemc2.mm";

theorem u1lemc3(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wvb;
    wva;
    ulemc3.1;
    wva;
    comid;
    u1lemc2;
  };

  return $|-$ $a C ( b ->1 a )$;
}
