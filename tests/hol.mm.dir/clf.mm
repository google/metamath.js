include "kl.mm";
include "tv.mm";
include "kc.mm";
include "ke.mm";
include "kbr.mm";
include "kt.mm";
include "wl.mm";
include "wc.mm";
include "eqtypi.mm";
include "weqi.mm";
include "ax-cb1.mm";
include "beta.mm";
include "a1i.mm";
include "hb.mm";
include "weq.mm";
include "wv.mm";
include "ht.mm";
include "a17i.mm";
include "hbl1.mm";
include "hbc.mm";
include "hbov.mm";
include "id.mm";
include "ceq2.mm";
include "oveq12.mm";
include "insti.mm";

theorem clf(hal: type al, hbe: type be, vx: var x, vy: var y, ta: term A, tb: term B, tc: term C) {
  assume clf.1: |- "A : be";
  assume clf.2: |- "C : al";
  assume clf.3: |- "[ x : al = C ] |= [ A = B ]";
  assume clf.4: |- "T. |= [ ( \\ x : al . B y : al ) = B ]";
  assume clf.5: |- "T. |= [ ( \\ x : al . C y : al ) = C ]";

  disjoint A y;
  disjoint B y;
  disjoint C y;
  disjoint x y;
  disjoint al x;
  disjoint al y;



  do {
    hal;
    vx;
    vy;
    hal;
    vx;
    ta;
    kl;
    #;
    hal;
    vx;
    tv;
    #;
    kc;
    #;
    ta;
    ke;
    kbr;
    #;
    @0;
    tc;
    kc;
    #;
    tb;
    ke;
    kbr;
    tc;
    kt;
    clf.2;
    hbe;
    @4;
    tb;
    hal;
    hbe;
    @0;
    tc;
    hal;
    hbe;
    vx;
    ta;
    clf.1;
    wl;
    #;
    clf.2;
    wc;
    #;
    hbe;
    ta;
    tb;
    @1;
    tc;
    ke;
    kbr;
    #;
    clf.1;
    clf.3;
    eqtypi;
    #;
    weqi;
    @3;
    kt;
    hal;
    vx;
    tb;
    kl;
    hal;
    vy;
    tv;
    #;
    kc;
    tb;
    ke;
    kbr;
    kt;
    clf.4;
    ax-cb1;
    #;
    hal;
    hbe;
    vx;
    ta;
    clf.1;
    beta;
    a1i;
    hal;
    hbe;
    hbe;
    hb;
    vx;
    @4;
    @9;
    tb;
    ke;
    kt;
    hbe;
    weq;
    #;
    @6;
    hal;
    vy;
    wv;
    #;
    @8;
    hal;
    hbe;
    hbe;
    hb;
    ht;
    ht;
    vx;
    ke;
    @9;
    kt;
    @11;
    @12;
    @10;
    a17i;
    hal;
    hal;
    hbe;
    vx;
    tc;
    @9;
    @0;
    kt;
    @5;
    clf.2;
    @12;
    hal;
    hal;
    hbe;
    vx;
    ta;
    @9;
    kt;
    clf.1;
    @12;
    @10;
    hbl1;
    clf.5;
    hbc;
    clf.4;
    hbov;
    hbe;
    hbe;
    hb;
    @2;
    ta;
    @4;
    ke;
    @7;
    tb;
    @11;
    hal;
    hbe;
    @0;
    @1;
    @5;
    hal;
    vx;
    wv;
    #;
    wc;
    clf.1;
    hal;
    hbe;
    @1;
    tc;
    @0;
    @7;
    @5;
    @13;
    @7;
    hal;
    @1;
    tc;
    @13;
    clf.2;
    weqi;
    id;
    ceq2;
    clf.3;
    oveq12;
    insti;
  };

  return |- "T. |= [ ( \\ x : al . A C ) = B ]";
}
