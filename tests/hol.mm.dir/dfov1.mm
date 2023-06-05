include "kbr.mm";
include "kc.mm";
include "ke.mm";
include "ax-cb1.mm";
include "hb.mm";
include "df-ov.mm";
include "a1i.mm";
include "ax-eqmp.mm";

theorem dfov1(hal: type al, hbe: type be, ta: term A, tb: term B, tf: term F, tr: term R) {
  assume dfov1.1: |- "F : ( al -> ( be -> bool ) )";
  assume dfov1.2: |- "A : al";
  assume dfov1.3: |- "B : be";
  assume dfov1.4: |- "R |= [ A F B ]";





  do {
    ta;
    tb;
    tf;
    kbr;
    #;
    tf;
    ta;
    kc;
    tb;
    kc;
    #;
    tr;
    dfov1.4;
    ke;
    @0;
    kc;
    @1;
    kc;
    tr;
    @0;
    tr;
    dfov1.4;
    ax-cb1;
    hal;
    hbe;
    hb;
    ta;
    tb;
    tf;
    dfov1.1;
    dfov1.2;
    dfov1.3;
    df-ov;
    a1i;
    ax-eqmp;
  };

  return |- "R |= ( ( F A ) B )";
}
