include "hb.mm";
include "tv.mm";
include "wv.mm";
include "ax-17.mm";
include "isfree.mm";

theorem ax17(hal: $type$ al, vx: $var$ x, ta: $term$ A) {
  assume ax17.1: $|- A : bool$;

  disjoint A x;
  disjoint al x;
  disjoint x y;
  disjoint A y;
  disjoint al y;

  let vy: $var$ y;

  do {
    hal;
    vx;
    vy;
    ta;
    ax17.1;
    hal;
    hb;
    vx;
    ta;
    hal;
    vy;
    tv;
    ax17.1;
    hal;
    vy;
    wv;
    ax-17;
    isfree;
  };

  return $|-$ $T. |= [ A ==> ( ! \ x : al . A ) ]$;
}
