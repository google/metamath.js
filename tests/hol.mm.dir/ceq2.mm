include "ht.mm";
include "ke.mm";
include "kbr.mm";
include "ax-cb1.mm";
include "eqid.mm";
include "ceq12.mm";

theorem ceq2(hal: type al, hbe: type be, ta: term A, tb: term B, tf: term F, tr: term R) {
  assume ceq12.1: |- "F : ( al -> be )";
  assume ceq12.2: |- "A : al";
  assume ceq2.3: |- "R |= [ A = B ]";





  do {
    hal;
    hbe;
    ta;
    tb;
    tf;
    tr;
    tf;
    ceq12.1;
    ceq12.2;
    hal;
    hbe;
    ht;
    tf;
    tr;
    ta;
    tb;
    ke;
    kbr;
    tr;
    ceq2.3;
    ax-cb1;
    ceq12.1;
    eqid;
    ceq2.3;
    ceq12;
  };

  return |- "R |= [ ( F A ) = ( F B ) ]";
}
