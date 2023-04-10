include "wa.mm";
include "ancom.mm";
include "bi1.mm";

theorem wancom(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    wvb;
    wva;
    wa;
    wva;
    wvb;
    ancom;
    bi1;
  };

  return $|- ( ( a ^ b ) == ( b ^ a ) ) = 1$;
}
