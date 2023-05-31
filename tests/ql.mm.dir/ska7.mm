include "wo.mm";
include "wa.mm";
include "anabs.mm";
include "bi1.mm";

theorem ska7(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wo;
    wa;
    wva;
    wva;
    wvb;
    anabs;
    bi1;
  };

  return $|-$ $( ( a ^ ( a v b ) ) == a ) = 1$;
}
