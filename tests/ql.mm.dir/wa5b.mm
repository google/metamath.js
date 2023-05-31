include "wa.mm";
include "wo.mm";
include "orabs.mm";
include "bi1.mm";

theorem wa5b(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wa;
    wo;
    wva;
    wva;
    wvb;
    orabs;
    bi1;
  };

  return $|-$ $( ( a v ( a ^ b ) ) == a ) = 1$;
}
