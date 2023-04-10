include "wo.mm";
include "ax-a2.mm";
include "comor1.mm";
include "bctr.mm";

theorem comor2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wo;
    wvb;
    wva;
    wo;
    wvb;
    wva;
    wvb;
    ax-a2;
    wvb;
    wva;
    comor1;
    bctr;
  };

  return $|- ( a v b ) C b$;
}
