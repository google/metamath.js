include "kl.mm";
include "kc.mm";
include "ke.mm";
include "kbr.mm";
include "ax-hbl1.mm";
include "a1i.mm";

theorem hbl1(hal: type al, hbe: type be, hga: type ga, vx: var x, ta: term A, tb: term B, tr: term R) {
  assume ax-hbl1.1: |- "A : ga";
  assume ax-hbl1.2: |- "B : al";
  assume hbl1.3: |- "R : bool";





  do {
    hal;
    vx;
    hbe;
    vx;
    ta;
    kl;
    #;
    kl;
    tb;
    kc;
    @0;
    ke;
    kbr;
    tr;
    hbl1.3;
    hal;
    hbe;
    hga;
    vx;
    ta;
    tb;
    ax-hbl1.1;
    ax-hbl1.2;
    ax-hbl1;
    a1i;
  };

  return '|-' "R |= [ ( \\ x : al . \\ x : be . A B ) = \\ x : be . A ]";
}
