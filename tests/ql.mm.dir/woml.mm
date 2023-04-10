include "wn.mm";
include "wo.mm";
include "wa.mm";
include "omlem1.mm";
include "omlem2.mm";
include "wlem3.1.mm";

theorem woml(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wn;
    wva;
    wvb;
    wo;
    #;
    wa;
    wo;
    @0;
    wva;
    wvb;
    omlem1;
    wva;
    wvb;
    omlem2;
    wlem3.1;
  };

  return $|- ( ( a v ( a ' ^ ( a v b ) ) ) == ( a v b ) ) = 1$;
}
