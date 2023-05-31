include "tv.mm";
include "wv.mm";
include "ax-17.mm";
include "ke.mm";
include "kbr.mm";
include "eqtypi.mm";
include "cbvf.mm";

theorem cbv(hal: $type$ al, hbe: $type$ be, vx: $var$ x, vy: $var$ y, ta: $term$ A, tb: $term$ B) {
  assume cbv.1: $|- A : be$;
  assume cbv.2: $|- [ x : al = y : al ] |= [ A = B ]$;

  disjoint A y;
  disjoint B x;
  disjoint x y;
  disjoint al x;
  disjoint al y;
  disjoint be y;
  disjoint y z;
  disjoint A z;
  disjoint x z;
  disjoint B z;
  disjoint al z;

  let vz: $var$ z;

  do {
    hal;
    hbe;
    vx;
    vy;
    vz;
    ta;
    tb;
    cbv.1;
    hal;
    hbe;
    vy;
    ta;
    hal;
    vz;
    tv;
    #;
    cbv.1;
    hal;
    vz;
    wv;
    #;
    ax-17;
    hal;
    hbe;
    vx;
    tb;
    @0;
    hbe;
    ta;
    tb;
    hal;
    vx;
    tv;
    hal;
    vy;
    tv;
    ke;
    kbr;
    cbv.1;
    cbv.2;
    eqtypi;
    @1;
    ax-17;
    cbv.2;
    cbvf;
  };

  return $|-$ $T. |= [ \ x : al . A = \ y : al . B ]$;
}
