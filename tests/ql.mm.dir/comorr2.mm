include "wo.mm";
include "comor2.mm";
include "comcom.mm";

theorem comorr2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wo;
    wvb;
    wva;
    wvb;
    comor2;
    comcom;
  };

  return $|- b C ( a v b )$;
}
