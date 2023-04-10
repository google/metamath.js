include "wo.mm";
include "leo.mm";
include "lecom.mm";

theorem comorr(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wo;
    wva;
    wvb;
    leo;
    lecom;
  };

  return $|-$ $a C ( a v b )$;
}
