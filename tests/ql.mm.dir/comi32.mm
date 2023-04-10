include "comid.mm";
include "com2i3.mm";

theorem comi32(wva: $term$ a, wvb: $term$ b) {
  assume comi32.1: $|- a C b$;





  do {
    wva;
    wvb;
    wva;
    comi32.1;
    wva;
    comid;
    com2i3;
  };

  return $|- a C ( b ->3 a )$;
}
