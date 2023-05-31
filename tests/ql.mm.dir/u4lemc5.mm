include "comid.mm";
include "u4lemc2.mm";

theorem u4lemc5(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wva;
    wvb;
    wva;
    comid;
    ulemc3.1;
    u4lemc2;
  };

  return $|-$ $a C ( a ->4 b )$;
}
