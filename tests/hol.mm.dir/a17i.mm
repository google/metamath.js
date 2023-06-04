include "kl.mm";
include "kc.mm";
include "ke.mm";
include "kbr.mm";
include "ax-17.mm";
include "a1i.mm";

theorem a17i(hal: type al, hbe: type be, vx: var x, ta: term A, tb: term B, tr: term R) {
  assume ax-17.1: |- "A : be";
  assume ax-17.2: |- "B : al";
  assume a17i.3: |- "R : bool";

  disjoint A x;



  do {
    hal;
    vx;
    ta;
    kl;
    tb;
    kc;
    ta;
    ke;
    kbr;
    tr;
    a17i.3;
    hal;
    hbe;
    vx;
    ta;
    tb;
    ax-17.1;
    ax-17.2;
    ax-17;
    a1i;
  };

  return '|-' "R |= [ ( \\ x : al . A B ) = A ]";
}
