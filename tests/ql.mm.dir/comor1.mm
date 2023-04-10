include "wo.mm";
include "comorr.mm";
include "comcom.mm";

theorem comor1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wo;
    wva;
    wvb;
    comorr;
    comcom;
  };

  return $|- ( a v b ) C a$;
}
