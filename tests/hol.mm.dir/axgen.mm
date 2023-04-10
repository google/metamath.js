include "kt.mm";
include "alrimiv.mm";

theorem axgen(hal: $type$ al, vx: $var$ x, tr: $term$ R) {
  assume axgen.1: $|- T. |= R$;

  disjoint al x;



  do {
    hal;
    vx;
    tr;
    kt;
    axgen.1;
    alrimiv;
  };

  return $|-$ $T. |= ( ! \ x : al . R )$;
}
