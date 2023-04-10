include "wo.mm";
include "comorr.mm";
include "oridm.mm";
include "cbtr.mm";

theorem comid(wva: $term$ a) {





  do {
    wva;
    wva;
    wva;
    wo;
    wva;
    wva;
    wva;
    comorr;
    wva;
    oridm;
    cbtr;
  };

  return $|-$ $a C a$;
}
