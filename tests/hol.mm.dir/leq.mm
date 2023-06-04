include "ht.mm";
include "kl.mm";
include "ke.mm";
include "weq.mm";
include "wl.mm";
include "eqtypi.mm";
include "dfov1.mm";
include "ax-leq.mm";
include "dfov2.mm";

theorem leq(hal: 'type' al, hbe: 'type' be, vx: 'var' x, ta: 'term' A, tb: 'term' B, tr: 'term' R) {
  assume leq.1: |- "A : be";
  assume leq.2: |- "R |= [ A = B ]";

  disjoint R x;



  do {
    hal;
    hbe;
    ht;
    #;
    @0;
    hal;
    vx;
    ta;
    kl;
    hal;
    vx;
    tb;
    kl;
    ke;
    tr;
    @0;
    weq;
    hal;
    hbe;
    vx;
    ta;
    leq.1;
    wl;
    hal;
    hbe;
    vx;
    tb;
    hbe;
    ta;
    tb;
    tr;
    leq.1;
    leq.2;
    eqtypi;
    #;
    wl;
    hal;
    hbe;
    vx;
    ta;
    tb;
    tr;
    leq.1;
    @1;
    hbe;
    hbe;
    ta;
    tb;
    ke;
    tr;
    hbe;
    weq;
    leq.1;
    @1;
    leq.2;
    dfov1;
    ax-leq;
    dfov2;
  };

  return '|-' "R |= [ \\ x : al . A = \\ x : al . B ]";
}
