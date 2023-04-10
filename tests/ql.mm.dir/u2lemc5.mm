include "comid.mm";
include "u2lemc2.mm";

theorem u2lemc5(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wva;
    wvb;
    wva;
    comid;
    ulemc3.1;
    u2lemc2;
  };

  return $|- a C ( a ->2 b )$;
}
