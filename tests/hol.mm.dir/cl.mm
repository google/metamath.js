include "tv.mm";
include "ke.mm";
include "kbr.mm";
include "eqtypi.mm";
include "wv.mm";
include "ax-17.mm";
include "clf.mm";

theorem cl(hal: 'type' al, hbe: 'type' be, vx: 'var' x, ta: 'term' A, tb: 'term' B, tc: 'term' C) {
  assume cl.1: |- "A : be";
  assume cl.2: |- "C : al";
  assume cl.3: |- "[ x : al = C ] |= [ A = B ]";

  disjoint B x;
  disjoint C x;
  disjoint al x;
  disjoint A y;
  disjoint x y;
  disjoint B y;
  disjoint C y;
  disjoint al y;

  let vy: var y;

  do {
    hal;
    hbe;
    vx;
    vy;
    ta;
    tb;
    tc;
    cl.1;
    cl.2;
    cl.3;
    hal;
    hbe;
    vx;
    tb;
    hal;
    vy;
    tv;
    #;
    hbe;
    ta;
    tb;
    hal;
    vx;
    tv;
    tc;
    ke;
    kbr;
    cl.1;
    cl.3;
    eqtypi;
    hal;
    vy;
    wv;
    #;
    ax-17;
    hal;
    hal;
    vx;
    tc;
    @0;
    cl.2;
    @1;
    ax-17;
    clf;
  };

  return '|-' "T. |= [ ( \\ x : al . A C ) = B ]";
}
